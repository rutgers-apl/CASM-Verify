import pyparse.pyparsing as pp
import config

returnStack = []
def pushReturn(str, loc, toks) :
    global returnStack
    returnStack.append(toks[0])

reg8 = \
    pp.Combine(pp.Suppress("%") + "al") \
    | pp.Combine(pp.Suppress("%") + "bl") \
    | pp.Combine(pp.Suppress("%") + "cl") \
    | pp.Combine(pp.Suppress("%") + "dl") \
    | pp.Combine(pp.Suppress("%") + "ah") \
    | pp.Combine(pp.Suppress("%") + "bh") \
    | pp.Combine(pp.Suppress("%") + "ch") \
    | pp.Combine(pp.Suppress("%") + "dh")

reg32 = \
    pp.Combine(pp.Suppress("%") + "eax") \
    | pp.Combine(pp.Suppress("%") + "ebx") \
    | pp.Combine(pp.Suppress("%") + "ecx") \
    | pp.Combine(pp.Suppress("%") + "edx") \
    | pp.Combine(pp.Suppress("%") + "esp") \
    | pp.Combine(pp.Suppress("%") + "ebp") \
    | pp.Combine(pp.Suppress("%") + "esi") \
    | pp.Combine(pp.Suppress("%") + "edi") \
    | pp.Combine(pp.Suppress("%") + "r8d") \
    | pp.Combine(pp.Suppress("%") + "r9d") \
    | pp.Combine(pp.Suppress("%") + "r10d") \
    | pp.Combine(pp.Suppress("%") + "r11d") \
    | pp.Combine(pp.Suppress("%") + "r12d") \
    | pp.Combine(pp.Suppress("%") + "r13d") \
    | pp.Combine(pp.Suppress("%") + "r14d") \
    | pp.Combine(pp.Suppress("%") + "r15d") \
    | pp.Combine(pp.Suppress("%") + "eip")

reg64 = \
    pp.Combine(pp.Suppress("%") + "rax") \
    | pp.Combine(pp.Suppress("%") + "rbx") \
    | pp.Combine(pp.Suppress("%") + "rcx") \
    | pp.Combine(pp.Suppress("%") + "rdx") \
    | pp.Combine(pp.Suppress("%") + "rsp") \
    | pp.Combine(pp.Suppress("%") + "rbp") \
    | pp.Combine(pp.Suppress("%") + "rsi") \
    | pp.Combine(pp.Suppress("%") + "rdi") \
    | pp.Combine(pp.Suppress("%") + "r8") \
    | pp.Combine(pp.Suppress("%") + "r9") \
    | pp.Combine(pp.Suppress("%") + "r10") \
    | pp.Combine(pp.Suppress("%") + "r11") \
    | pp.Combine(pp.Suppress("%") + "r12") \
    | pp.Combine(pp.Suppress("%") + "r13") \
    | pp.Combine(pp.Suppress("%") + "r14") \
    | pp.Combine(pp.Suppress("%") + "r15") \
    | pp.Combine(pp.Suppress("%") + "rip") \

reg128 = \
    pp.Combine(pp.Suppress("%") + "xmm0") \
    | pp.Combine(pp.Suppress("%") + "xmm1") \
    | pp.Combine(pp.Suppress("%") + "xmm2") \
    | pp.Combine(pp.Suppress("%") + "xmm3") \
    | pp.Combine(pp.Suppress("%") + "xmm4") \
    | pp.Combine(pp.Suppress("%") + "xmm5") \
    | pp.Combine(pp.Suppress("%") + "xmm6") \
    | pp.Combine(pp.Suppress("%") + "xmm7") 

register = reg8 | reg32 | reg64 | reg128

immediate = pp.Combine(pp.Suppress("$") + pp.Literal("0x") + pp.Word(pp.hexnums)) | pp.Combine(pp.Suppress("$") + pp.Optional("-") + pp.Word(pp.nums))

memory_offset = pp.Combine(pp.Optional("-") + pp.Word(pp.nums))
memory_base = register
memory_index = register
memory_scale = pp.Or(["1", "2", "4", "8"])

label = pp.Combine(pp.Literal("L$") + pp.Word(pp.alphas, pp.alphanums + "_"))

memory = pp.Group(\
    pp.Optional(memory_offset, default = "OFFSET") \
    + pp.Suppress("(") + pp.Optional(memory_base, default = "BASE") \
    + pp.Optional(pp.Suppress(",") + memory_index \
    + pp.Optional(pp.Suppress(",") + memory_scale)) \
    + pp.Suppress(")"))

Operands =  memory | register | immediate

JumpInstList = pp.Word("j", pp.alphas)

JumpInstructions = JumpInstList + label

BinOpInstList = pp.Word(pp.alphas)

BinOpInstructions = BinOpInstList + Operands + pp.Suppress(",") + Operands

UnOpInstList = pp.Word(pp.alphas)

UnOpInstructions = UnOpInstList + Operands

TripOpInstList = pp.Word(pp.alphas)

TripOpInstructions = TripOpInstList + Operands + pp.Suppress(",") + Operands + pp.Suppress(",") + Operands

x86AsmInst = pp.Group(TripOpInstructions | JumpInstructions | BinOpInstructions | UnOpInstructions)

x86AsmLanguage = pp.OneOrMore(x86AsmInst)

def ASMToX86Parse(asm) :
    global returnStack
    myInstructions = x86AsmLanguage.parseString(asm, parseAll=True)
    return (myInstructions)
