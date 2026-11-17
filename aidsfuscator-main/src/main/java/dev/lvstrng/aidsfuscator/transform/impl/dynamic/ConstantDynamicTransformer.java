package dev.lvstrng.aidsfuscator.transform.impl.dynamic;

import dev.lvstrng.aidsfuscator.context.Context;
import dev.lvstrng.aidsfuscator.exclude.impl.Exclusions;
import dev.lvstrng.aidsfuscator.property.Property;
import dev.lvstrng.aidsfuscator.transform.Setting;
import dev.lvstrng.aidsfuscator.transform.Transformer;
import dev.lvstrng.aidsfuscator.tree.impl.JClass;
import dev.lvstrng.aidsfuscator.utils.ASMUtils;
import dev.lvstrng.aidsfuscator.utils.InsnBuilder;
import org.objectweb.asm.ConstantDynamic;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;

public class ConstantDynamicTransformer extends Transformer {
    private static final String BSM_DESC =
            "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/Class;Ljava/lang/Object;I)Ljava/lang/Object;";

    private final Setting<Boolean> encryptIntegers = setting("encryptIntegers", true);
    private final Setting<Boolean> encryptLongs = setting("encryptLongs", true);
    private final Setting<Boolean> encryptStrings = setting("encryptStrings", true);
    private final Setting<Boolean> excludeLowSignificant = setting("excludeLowSignificant", true);
    private final Setting<Integer> minStringLength = setting("minStringLength", 4);

    public ConstantDynamicTransformer() {
        super("Constant Dynamics", "ConstantDynamicTransformer");
    }

    @Override
    public void transform(Context context) {
        for(var clazz : context.classes()) {
            if(clazz.version() < V11)
                continue;

            if(Exclusions.CONSTANT_DYNAMIC.excluded(clazz))
                continue;

            var bsmName = context.dictionary().newMethodName(clazz, BSM_DESC);
            var bsmHandle = new Handle(H_INVOKESTATIC, clazz.name(), bsmName, BSM_DESC, false);
            var classKeyI = random.nextInt();
            var classKeyL = random.nextLong();
            var changed = false;

            for(var method : clazz.methods()) {
                if(Exclusions.CONSTANT_DYNAMIC.excluded(method))
                    continue;

                for(var insn : method.insns()) {
                    var replacement = toConstantDynamic(context, insn, bsmHandle, classKeyI, classKeyL);
                    if(replacement == null)
                        continue;

                    method.insns().insertBefore(insn, replacement);
                    method.insns().remove(insn);
                    markChange();
                    changed = true;
                }
                method.reinitUnsafeInstructions();
            }

            if(!changed) {
                context.dictionary().revertMethod();
                continue;
            }

            generateBsm(clazz, bsmName, classKeyI, classKeyL);
        }
    }

    private LdcInsnNode toConstantDynamic(Context context, AbstractInsnNode insn, Handle bsm, int classKeyI, long classKeyL) {
        LdcInsnNode ldc;

        if(encryptIntegers.value() && ASMUtils.isIntPush(insn)) {
            if(excludeLowSignificant.value() && ASMUtils.isIconst(insn))
                return null;
            if(context.properties().get(insn).has(Property.IGNORE_INTEGER))
                return null;

            var key = random.nextInt();
            var payload = ASMUtils.getInt(insn) ^ key ^ classKeyI;
            ldc = new LdcInsnNode(new ConstantDynamic("i", "I", bsm, payload, key));
        } else if(encryptLongs.value() && ASMUtils.isLongPush(insn)) {
            if(context.properties().get(insn).has(Property.IGNORE_LONG))
                return null;

            var key = random.nextInt();
            var payload = ASMUtils.getLong(insn) ^ (classKeyL ^ (long) key);
            ldc = new LdcInsnNode(new ConstantDynamic("j", "J", bsm, payload, key));
        } else if(encryptStrings.value() && insn instanceof LdcInsnNode src && src.cst instanceof String s) {
            if(s.length() < minStringLength.value() || s.length() > Character.MAX_VALUE)
                return null;
            if(context.properties().get(insn).has(Property.IGNORE_STRING))
                return null;

            var key = random.nextInt();
            var chars = s.toCharArray();
            for(var i = 0; i < chars.length; i++)
                chars[i] ^= (char) (key ^ classKeyI ^ i);

            ldc = new LdcInsnNode(new ConstantDynamic("s", "Ljava/lang/String;", bsm, new String(chars), key));
        } else {
            return null;
        }

        context.properties().add(ldc, Property.IGNORE_REF_OBFUSCATION);
        return ldc;
    }

    private void generateBsm(JClass clazz, String bsmName, int classKeyI, long classKeyL) {
        var bsm = clazz.createMethod(ACC_PUBLIC | ACC_STATIC, bsmName, BSM_DESC);
        bsm.setMaxLocals(5);

        var charsVar = bsm.allocVar(Type.getType("[C"));
        var iVar = bsm.allocVar(Type.INT_TYPE);

        var longBranch = new LabelNode();
        var stringBranch = new LabelNode();
        var loop = new LabelNode();
        var loopExit = new LabelNode();

        new InsnBuilder(bsm.insns())
                ._var(ALOAD, 2)
                .field(GETSTATIC, "java/lang/Integer", "TYPE", "Ljava/lang/Class;")
                .jump(IF_ACMPNE, longBranch)
                ._var(ALOAD, 3)
                .type(CHECKCAST, "java/lang/Integer")
                .method(INVOKEVIRTUAL, "java/lang/Integer", "intValue", "()I")
                ._var(ILOAD, 4)
                .ixor()
                ._int(classKeyI)
                .ixor()
                .method(INVOKESTATIC, "java/lang/Integer", "valueOf", "(I)Ljava/lang/Integer;")
                ._areturn()

                .label(longBranch)
                ._var(ALOAD, 2)
                .field(GETSTATIC, "java/lang/Long", "TYPE", "Ljava/lang/Class;")
                .jump(IF_ACMPNE, stringBranch)
                ._var(ALOAD, 3)
                .type(CHECKCAST, "java/lang/Long")
                .method(INVOKEVIRTUAL, "java/lang/Long", "longValue", "()J")
                ._var(ILOAD, 4)
                .i2l()
                ._long(classKeyL)
                .lxor()
                .lxor()
                .method(INVOKESTATIC, "java/lang/Long", "valueOf", "(J)Ljava/lang/Long;")
                ._areturn()

                .label(stringBranch)
                ._var(ALOAD, 3)
                .type(CHECKCAST, "java/lang/String")
                .method(INVOKEVIRTUAL, "java/lang/String", "toCharArray", "()[C")
                ._var(ASTORE, charsVar)
                ._int(0)
                ._var(ISTORE, iVar)
                .label(loop)
                ._var(ILOAD, iVar)
                ._var(ALOAD, charsVar)
                .arraylength()
                .jump(IF_ICMPGE, loopExit)
                ._var(ALOAD, charsVar)
                ._var(ILOAD, iVar)
                ._var(ALOAD, charsVar)
                ._var(ILOAD, iVar)
                .caload()
                ._var(ILOAD, 4)
                .ixor()
                ._int(classKeyI)
                .ixor()
                ._var(ILOAD, iVar)
                .ixor()
                .i2c()
                .castore()
                .iinc(iVar, 1)
                ._goto(loop)
                .label(loopExit)
                .type(NEW, "java/lang/String")
                .dup()
                ._var(ALOAD, charsVar)
                .method(INVOKESPECIAL, "java/lang/String", "<init>", "([C)V")
                .method(INVOKEVIRTUAL, "java/lang/String", "intern", "()Ljava/lang/String;")
                ._areturn();

        clazz.reinsertRandomly(random, bsm);
    }
}
