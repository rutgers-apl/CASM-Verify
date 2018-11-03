import x86parse
import x86todsl8bit

test = "addl (%rsp), %ebx"
insts = x86parse.ASMToX86Parse(test)
dsl = x86todsl8bit.ConvertToDsl(insts)

for d in dsl :
    d.SetProgramOrigin("P", False)
    print(d.ToString())
