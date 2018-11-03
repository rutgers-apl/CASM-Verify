from x86todslHelper import *
import dslinstructions
import dslparse
import config
import sys

def LoadFromMemoryString(address, numBytes, name) :
    tempString = ""
    # For the number of bytes, keep adding address and merge.
    memIndexSize = ":64"

    if numBytes == 1 :
        tempString = name + "= mem:8[" + address + "];\n"
    else :
        tempString = name + " = merge("
        for offset in range(0, numBytes) :
            if offset > 0 : tempString = tempString + ", "
            tempString = tempString + "mem:8[" + address + " + " + str(numBytes - 1 - offset) + memIndexSize + "]"
        tempString = tempString + ");\n"

    return tempString

def StoreToMemoryString(address, numBytes, toStore) :
    tempString = ""
    # For the number of bytes, keep adding address and merge.
    memIndexSize = ":64"

    if numBytes == 1 :
        tempString = "mem:8[" + address + "] = " + toStore + ");\n"
    else :
        for offset in range(0, numBytes) :
            memOffset = str(offset) + memIndexSize
            splitLowerBase = str(offset * 8)
            splitHigherBase = str(offset * 8 + 7)
            tempString = tempString + "mem:8[" + address + " + " + memOffset + "] = split(" + toStore + ", " + splitLowerBase + ", " + splitHigherBase + ");\n"

    return tempString

def SetupOperand8Bit(x) :
    oldDest = "oldDest8"; tempString = ""
    if (isImmediate(x[1]) or Is8Register(x[1])) and Is8Register(x[2]) :
        source = x[1] + ":8"; dest = x[2] + ":8"
        addr = ""
    elif (isImmediate(x[1]) or Is8Register(x[1])) and IsMemory(x[2]) :
        source = x[1] + ":8"; dest = "tempDest:8"
        addr = CalculateAddress(x[2])
        tempString = dest + " = mem:8[" + addr + "];\n"
    elif IsMemory(x[1]) and Is8Register(x[2]) :
        source = "tempSource:8"; dest = x[2] + ":8"
        addr = CalculateAddress(x[1])
        tempString = source + " = mem:8[" + addr + "];\n"
    else : sys.exit("Convertcmpb operand error: %s" % (x))

    return source, dest, oldDest, addr, tempString

def SetupOperand64Bit(x) :
    oldDest = "oldDest64:64"; tempString = ""
    
    if (isImmediate(x[1]) or Is64Register(x[1])) and Is64Register(x[2]) :
        source = x[1] + ":64"; dest = x[2] + ":64"
        addr = ""
    elif (isImmediate(x[1]) or Is64Register(x[1])) and IsMemory(x[2]) :
        source = x[1] + ":64"; dest = "tempDest64:64"
        addr = CalculateAddress(x[2])
        tempString = LoadFromMemoryString(addr, 8, dest)
    elif IsMemory(x[1]) and Is64Register(x[2]) :
        source = "tempSource64:64"; dest = x[2] + ":64"
        addr = CalculateAddress(x[1])
        tempString = LoadFromMemoryString(addr, 8, source)
    else : sys.exit("Convertsubl operand error: %s" % (x))

    return source, dest, oldDest, addr, tempString

def SaveToOperand64Bit(x, source, dest, oldDest, addr) :
    if (isImmediate(x[1]) or Is64Register(x[1])) and Is64Register(x[2]) :
        return Get32BitRepFromRegister(x[2])[0] + " = " + "split(" + dest + ", 0, 31);\n"
    elif (isImmediate(x[1]) or Is64Register(x[1])) and IsMemory(x[2]) :
        return StoreToMemoryString(addr, 8, dest)
    elif IsMemory(x[1]) and Is64Register(x[2]) :
        return Get32BitRepFromRegister(x[2])[0] + " = " + "split(" + dest + ", 0, 31);\n"

def SetupOperand32Bit(x) :
    oldDest = "oldDest"; tempString = ""
    
    if (isImmediate(x[1]) or Is32Register(x[1])) and Is32Register(x[2]) :
        source = x[1]; dest = x[2]
        addr = ""
    elif (isImmediate(x[1]) or Is32Register(x[1])) and IsMemory(x[2]) :
        source = x[1]; dest = "tempDest"
        addr = CalculateAddress(x[2])
        tempString = LoadFromMemoryString(addr, 4, dest)
    elif IsMemory(x[1]) and Is32Register(x[2]) :
        source = "tempSource"; dest = x[2]
        addr = CalculateAddress(x[1])
        tempString = LoadFromMemoryString(addr, 4, source)
    else : sys.exit("SetupOperand32Bit operand error: %s" % (x))
    
    return source, dest, oldDest, addr, tempString

def SaveToOperand32Bit(x, source, dest, oldDest, addr) :
    if config.Is64BitArch() :
        if (isImmediate(x[1]) or Is32Register(x[1])) and Is32Register(x[2]) :
            return Get64BitRepFromRegister(x[2])[0] + " = " + "zeroext(" + dest + ", 32);\n"
        elif (isImmediate(x[1]) or Is32Register(x[1])) and IsMemory(x[2]) :
            return StoreToMemoryString(addr, 4, dest)
        elif IsMemory(x[1]) and Is32Register(x[2]) :
            return Get64BitRepFromRegister(x[2])[0] + " = " + "zeroext(" + dest + ", 32);\n"
    elif config.Is32BitArch() :
        if (isImmediate(x[1]) or Is32Register(x[1])) and Is32Register(x[2]) :
            return ""
        elif (isImmediate(x[1]) or Is32Register(x[1])) and IsMemory(x[2]) :
            return StoreToMemoryString(addr, 4, dest)
        elif IsMemory(x[1]) and Is32Register(x[2]) :
            return ""
    

def SetupOperandForShifts64Bit(x) :
    tempString = ""; oldDest = "oldDest64:64"
    
    if isImmediate(x[1]) and Is64Register(x[2]) :
        source = x[1] + ":64"; dest = x[2] + ":64"
        addr = ""
    elif isImmediate(x[1]) and IsMemory(x[2]) :
        source = x[1] + ":64"; dest = "tempDest64:64"
        addr = CalculateAddress(x[2])
        tempString = LoadFromMemoryString(addr, 8, dest)
    else : sys.exit("Convertshrq operand error: %s" % (x))

    return source, dest, oldDest, addr, tempString

def SaveToOperandForShifts64Bit(x, source, dest, oldDest, addr) :
    if isImmediate(x[1]) and Is64Register(x[2]) :
        return Get32BitRepFromRegister(x[2])[0] + " = " + "split(" + dest + ", 0, 31);\n"
    elif isImmediate(x[1]) and IsMemory(x[2]) :
        return StoreToMemoryString(addr, 8, dest)

def SetupOperandForShifts32Bit(x) :
    oldDest = "oldDest"; tempString = ""
    
    if isImmediate(x[1]) and Is32Register(x[2]) :
        source = x[1]; dest = x[2]
        addr = ""
    elif isImmediate(x[1]) and IsMemory(x[2]) :
        source = x[1]; dest = "tempDest"
        addr = CalculateAddress(x[2])
        tempString = LoadFromMemoryString(addr, 4, dest)
    else : sys.exit("ConvertRorl operand error: %s" % (x))
    
    return source, dest, oldDest, addr, tempString

def SaveToOperandForShifts32Bit(x, source, dest, oldDest, addr) :
    if config.Is64BitArch() :
        if isImmediate(x[1]) and Is32Register(x[2]) :
            return Get64BitRepFromRegister(x[2])[0] + " = " + "zeroext(" + dest + ", 32);\n"
        elif isImmediate(x[1]) and IsMemory(x[2]) :
            return StoreToMemoryString(addr, 4, dest)
    elif config.Is32BitArch() :
        if isImmediate(x[1]) and Is32Register(x[2]) :
            return ""
        elif isImmediate(x[1]) and IsMemory(x[2]) :
            return StoreToMemoryString(addr, 4, dest)

##### 32 bit operations #####

def ConvertRorl(x) :
    source, dest, oldDest, addr, tempString = SetupOperandForShifts32Bit(x)
    tempString = tempString + (dest + " = " + dest + " >>> " + source + ";\n" +
                               SaveToOperandForShifts32Bit(x, source, dest, oldDest, addr))

    # Add Flags
    if int(x[1], 0) == 1 : tempString = tempString + "of:1 = split(" + dest + ", 31, 31) ^ split(" + dest + ", 30, 30);\n"
    else : tempString = tempString + "of:1 = builtin_undef;\n"
    tempString = tempString + ("cf:1 = split(" + dest + ", 31, 31);\n" +
                               "zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n" +
                               "sf:1 = split(" + dest + ", 31, 31);\n")

    return dslparse.dslToAst(tempString)


def ConvertRoll(x) :
    source, dest, oldDest, addr, tempString = SetupOperandForShifts32Bit(x)
    tempString = tempString + (dest + " = " + dest + " <<< " + source + ";\n" +
                               SaveToOperandForShifts32Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + "cf:1 = split(" + dest + ", 0, 0);\n"
    if int(x[1], 0) == 1 : tempString = tempString + "of:1 = split(" + dest + ", 31, 31) ^ cf:1;\n"
    else : tempString = tempString + "of:1 = builtin_undef;\n"
    tempString = tempString + ("zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n" +
                               "sf:1 = split(" + dest + ", 31, 31);\n")
    return dslparse.dslToAst(tempString)


def ConvertShrl(x) :
    source, dest, oldDest, addr, tempString = SetupOperandForShifts32Bit(x)
    tempString = tempString + (oldDest + " = " + dest + ";\n" + 
                               dest + " = " + dest + " >> " + source + ";\n" +
                               SaveToOperandForShifts32Bit(x, source, dest, oldDest, addr))

    # Add flags
    if int(x[1], 0) == 1 : tempString = tempString + "of:1 = split(" + oldDest + ", 31, 31);\n"
    else : tempString = tempString + "of:1 = builtin_undef;\n"
    tempString = tempString + ("cf:1 = split(" + oldDest + ", " + str(int(x[1], 0) - 1) + ", " + str(int(x[1], 0) - 1) + ");\n" +
                               "zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n" +
                               "sf:1 = split(" + dest + ", 31, 31);\n")
    return dslparse.dslToAst(tempString)


def ConvertShll(x) :
    source, dest, oldDest, addr, tempString = SetupOperandForShifts32Bit(x)
    tempString = tempString + (oldDest + " = " + dest + ";\n" + 
                               dest + " = " + dest + " << " + source + ";\n" +
                               SaveToOperandForShifts32Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + "cf:1 = split(" + dest + ", 31, 31);\n"
    if int(x[1], 0) == 1 : tempString = tempString + "of:1 = split(" + dest + ", 31, 31) ^ cf:1;\n"
    else : tempString = tempString + "of:1 = builtin_undef;\n"
    tempString = tempString + ("zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n" +
                               "sf:1 = split(" + dest + ", 31, 31);\n")
    return dslparse.dslToAst(tempString)


def ConvertAddl(x) :
    source, dest, oldDest, addr, tempString = SetupOperand32Bit(x)
    tempString = tempString + (oldDest + " = " + dest + ";\n" +
                               dest + " = " + dest + " + " + source + ";\n" +
                               SaveToOperand32Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + ("zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n" +
                               "cf_part1:1 = " + dest + " < " + oldDest + " ? 1:1 : 0:1;\n" + 
                               "cf_part2:1 = " + dest + " < " + source + " ? 1:1 : 0:1;\n" + 
                               "cf:1 = cf_part1:1 | cf_part2:1;\n" +
                               "of_part1:1 = split(" + oldDest + ", 31, 31) == split(" + source + ", 31, 31) ? 1:1 : 0:1;\n" + 
                               "of_part2:1 = split(" + source + ", 31, 31) != split(" + dest + ", 31, 31) ? 1:1 : 0:1;\n" + 
                               "of:1 = of_part1:1 & of_part2:1;\n" +
                               "sf:1 = split(" + dest + ", 31, 31);\n")
    return dslparse.dslToAst(tempString)


def ConvertAdcl(x) :
    source, dest, oldDest, addr, tempString = SetupOperand32Bit(x)
    tempString = tempString + (oldDest + " = " + dest + ";\n" +
                               dest + " = " + dest + " + " + source + " + zeroext(cf:1, 31);\n" +
                               SaveToOperand32Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + ("zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n" +
                               "cf_part1:1 = " + dest + " < " + oldDest + " ? 1:1 : 0:1;\n" +
                               "cf_part2:1 = " + dest + " < " + source + " ? 1:1 : 0:1;\n" +
                               "cf:1 = cf_part1:1 | cf_part2:1;\n" +
                               "of_part1:1 = split(" + oldDest + ", 31, 31) == split(" + source + ", 31, 31) ? 1:1 : 0:1;\n" +
                               "of_part2:1 = split(" + source + ", 31, 31) != split(" + dest + ", 31, 31) ? 1:1 : 0:1;\n" +
                               "of:1 = of_part1:1 & of_part2:1;\n" +
                               "sf:1 = split(" + dest + ", 31, 31);\n")
    return dslparse.dslToAst(tempString)


def ConvertSubl(x) :
    source, dest, oldDest, addr, tempString = SetupOperand32Bit(x)
    tempString = tempString + (oldDest + " = " + dest + ";\n" +
                               dest + " = " + dest + " - " + source + ";\n" +
                               SaveToOperand32Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + ("zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n" +
                               "of_part1:1 = split(" + oldDest + ", 31, 31) != split(" + source + ", 31, 31) ? 1:1 : 0:1;\n" +
                               "of_part2:1 = split(" + source + ", 31, 31) == split(" + dest + ", 31, 31) ? 1:1 : 0:1;\n" +
                               "of:1 = of_part1:1 & of_part2:1;\n" +
                               "cf:1 = " + source + " > " + oldDest + " ? 1:1 : 0:1;\n" +
                               "sf:1 = split(" + dest + ", 31, 31);\n")
    return dslparse.dslToAst(tempString)


def ConvertSbbl(x) :
    source, dest, oldDest, addr, tempString = SetupOperand32Bit(x)
    tempString = tempString + (oldDest + " = " + dest + ";\n" +
                               dest + " = " + dest + " - " + source + " - zeroext(cf:1, 31)" + ";\n" +
                               SaveToOperand32Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + ("zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n" +
                               "of_part1:1 = split(" + oldDest + ", 31, 31) != split(" + source + ", 31, 31) ? 1:1 : 0:1;\n" +
                               "of_part2:1 = split(" + source + ", 31, 31) == split(" + dest + ", 31, 31) ? 1:1 : 0:1;\n" +
                               "of:1 = of_part1:1 & of_part2:1;\n" +
                               "cf:1 = " + source + " > " + oldDest + " ? 1:1 : 0:1;\n" +
                               "sf:1 = split(" + dest + ", 31, 31);\n")
    return dslparse.dslToAst(tempString)


def ConvertXorl(x) :
    source, dest, oldDest, addr, tempString = SetupOperand32Bit(x)
    tempString = tempString + (dest + " = " + dest + " ^ " + source + ";\n" +
                               SaveToOperand32Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + ("zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n" +
                               "cf:1 = 0:1;\n" +
                               "of:1 = 0:1;\n" +
                               "sf:1 = split(" + dest + ", 31, 31);\n")
    return dslparse.dslToAst(tempString)


def ConvertAndl(x) :
    source, dest, oldDest, addr, tempString = SetupOperand32Bit(x)
    tempString = tempString + (dest + " = " + dest + " & " + source + ";\n" +
                               SaveToOperand32Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + ("zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n" +
                               "cf:1 = 0:1;\n" +
                               "of:1 = 0:1;\n" +
                               "sf:1 = split(" + dest + ", 31, 31);\n")
    return dslparse.dslToAst(tempString)


def ConvertMovl(x) :
    source, dest, oldDest, addr, tempString = SetupOperand32Bit(x)
    tempString = tempString + (dest + " = " + source + ";\n" +
                               SaveToOperand32Bit(x, source, dest, oldDest, addr))
    return dslparse.dslToAst(tempString)

def ConvertCmovccl(x, cc) :
    source, dest, oldDest, addr, tempString = SetupOperand32Bit(x)
    tempString = tempString + (dest + " = " + cc + " ? " + source + " : " + dest + ";\n" +
                               SaveToOperand32Bit(x, source, dest, oldDest, addr))
    return dslparse.dslToAst(tempString)
    

def ConvertCmovzl(x) :
    return ConvertCmovccl(x, "zf:1 == 1:1")

def ConvertCmovnzl(x) :
    return ConvertCmovccl(x, "zf:1 == 0:1")

def ConvertCmovncl(x) :
    return ConvertCmovccl(x, "cf:1 == 0:1")

def ConvertCmovnol(x) :
    return ConvertCmovccl(x, "of:1 == 0:1")

def ConvertCmovel(x) :
    return ConvertCmovzl(x)

def ConvertCmovnel(x) :
    return ConvertCmovnzl(x)

def ConvertCmovgel(x) :
    return ConvertCmovccl(x, "sf:1 == of:1")

def ConvertCmovll(x) :
    return ConvertCmovccl(x, "sf:1 != of:1")

def ConvertCmovlel(x) :
    return ConvertCmovccl(x, "((sf:1 ^ of:1) | zf:1) == 1:1")

def ConvertCmovgl(x) :
    return ConvertCmovccl(x, "((sf:1 ^ of:1) | zf:1) == 0:1")


def ConvertMovzbl(x) :
    if IsMemory(x[1]) and Is32Register(x[2]) :
        addr = CalculateAddress(x[1])
        dest = x[2]
        tempString = dest + " = zeroext(mem:8[" + addr + "], 24);\n"

        if config.Is64BitArch() :
            dest64 = Get64BitRepFromRegister(x[2])[0]
            tempString = tempString + dest64 + " = " + "zeroext(" + dest + ", 32);\n"

    elif Is8Register(x[1]) and Is32Register(x[2]) :
        if x[1] in reg8lowRev : source = "split(" + reg32[reg8lowRev[x[1]]] + ", 0, 7)"
        elif x[1] in reg8highRev : source = "split(" + reg32[reg8highRev[x[1]]] + ", 8, 15)"
        dest = x[2]
        tempString = dest + " = zeroext(" + source + ", 24);\n"
        
        if config.Is64BitArch() :
            dest64 = Get64BitRepFromRegister(x[2])[0]
            tempString = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    else : sys.exit("Convertmovzbl operand error: %s" % (x))

    return dslparse.dslToAst(tempString)


def ConvertCmpl(x) :
    temp = "tempCmpl"
    source, dest, oldDest, addr, tempString = SetupOperand32Bit(x)
    tempString = tempString + temp + " = " + dest + " - " + source + ";\n"
            
    # Add flags
    tempString = tempString + ("zf:1 = " + temp + " == 0 ? 1:1 : 0:1;\n" +
                               "of_part1:1 = split(" + source + ", 31, 31) != split(" + dest + ", 31, 31) ? 1:1 : 0:1;\n" +
                               "of_part2:1 = split(" + dest + ", 31, 31) == split(" + temp + ", 31, 31) ? 1:1 : 0:1;\n" +
                               "of:1 = of_part1:1 & of_part2:1;\n" +
                               "cf:1 = " + source + " > " + dest + " ? 1:1 : 0:1;\n" +
                               "sf:1 = split(" + temp + ", 31, 31);\n")
    return dslparse.dslToAst(tempString)


def ConvertCmpb(x) :
    temp = "tempCmpb:8"
    source, dest, oldDest, addr, tempString = SetupOperand8Bit(x)
    tempString = tempString + temp + " = " + dest + " - " + source + ";\n"

    # Add flags
    tempString = tempString + ("zf:1 = " + temp + " == 0:8 ? 1:1 : 0:1;\n" +
                               "of_part1:1 = split(" + source + ", 7, 7) != split(" + dest + ", 7, 7) ? 1:1 : 0:1;\n" +
                               "of_part2:1 = split(" + dest + ", 7, 7) == split(" + temp + ", 7, 7) ? 1:1 : 0:1;\n" +
                               "of:1 = of_part1:1 & of_part2:1;\n" +
                               "cf:1 = " + source + " > " + dest + " ? 1:1 : 0:1;\n" +
                               "sf:1 = split(" + temp + ", 7, 7);\n")
    return dslparse.dslToAst(tempString)


def ConvertDecl(x) :
    oldDest = "oldDest"
    if Is32Register(x[1]) :
        dest = x[1]
        tempString = (oldDest + " = " + dest + ";\n" + 
                      dest + " = " + dest + " - 1;\n")

        if config.Is64BitArch() :
            dest64 = Get64BitRepFromRegister(x[1])[0]
            tempString = tempString + dest64 + " = " + "zeroext(" + dest + ", 32);\n"


    elif IsMemory(x[1]) :
        dest = "tempDest"
        addr = CalculateAddress(x[1])
        tempString = (LoadFromMemoryString(addr, 4, dest) +
                      oldDest + " = " + dest + ";\n" +
                      dest + " = " + dest + " - 1;\n" +
                      StoreToMemoryString(addr, 4, dest))

    else : sys.exit("Convertdecl operand error: %s" % (x))

    # Add flags
    tempString = tempString + ("zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n" +
                               "cf:1 = 1 > " + oldDest + " ? 1:1 : 0:1;\n" +
                               "of_part1:1 = 0 != split(" + oldDest + ", 31, 31) ? 1:1 : 0:1;\n" +
                               "of_part2:1 = split(" + oldDest + ", 31, 31) == split(" + dest + ", 31, 31) ? 1:1 : 0:1;\n" +
                               "of:1 = of_part1:1 & of_part2:1;\n" +
                               "sf:1 = split(" + dest + ", 31, 31);\n")
    return dslparse.dslToAst(tempString)


def ConvertBswapl(x) :
    dest = x[1]
    dest64 = Get64BitRepFromRegister(x[1])[0]
    tempString = (dest + " = merge(split(" + dest + ", 0, 7), merge(split(" + dest + ", 8, 15), merge(split(" + dest + ", 16, 23), split(" + dest + ", 24, 31))));\n" +
                  dest64 + " = zeroext(" + dest + ", 32);\n")
    return dslparse.dslToAst(tempString)


##### 64 bit operation
def ConvertPushq(x) :
    if Is64Register(x[1]) :
        dest = x[1] + ":64"
        addr = "rsp:64"
        tempString = (addr + " = " + addr + " - 8:64" + ";\n" +
                      StoreToMemoryString(addr, 8, dest))
    else : sys.exit("Convertpushq operand error: %s" % (x))

    return dslparse.dslToAst(tempString)

# Available operand combination
# popq reg : implemented
def ConvertPopq(x) :
    if Is64Register(x[1]) :
        addr = "rsp:64"
        dest = x[1] + ":64"
        tempString = (LoadFromMemoryString(addr, 8, dest) +
                      addr + " = " + addr + " + 8:64" + ";\n")
    else : sys.exit("Convertpopq operand error: %s" % (x))

    return dslparse.dslToAst(tempString)
    

def ConvertSubq(x) :
    source, dest, oldDest, addr, tempString = SetupOperand64Bit(x)
    tempString = tempString + (oldDest + " = " + dest + ";\n" +
                               dest + " = " + dest + " - " + source + ";\n" +
                               SaveToOperand64Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + ("zf:1 = " + dest + " == 0:64 ? 1:1 : 0:1;\n" +
                               "of_part1:1 = split(" + oldDest + ", 63, 63) != split(" + source + ", 63, 63) ? 1:1 : 0:1;\n" +
                               "of_part2:1 = split(" + source + ", 63, 63) == split(" + dest + ", 63, 63) ? 1:1 : 0:1;\n" +
                               "of:1 = of_part1:1 & of_part2:1;\n" +
                               "cf:1 = " + source + " > " + oldDest + " ? 1:1 : 0:1;\n" +
                               "sf:1 = split(" + dest + ", 63, 63);\n")

    return dslparse.dslToAst(tempString)


def ConvertSbbq(x) :
    source, dest, oldDest, addr, tempString = SetupOperand64Bit(x)
    tempString = tempString + (oldDest + " = " + dest + ";\n" +
                               dest + " = " + dest + " - " + source + " - zeroext(cf:1, 63);\n" +
                               SaveToOperand64Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + ("zf:1 = " + dest + " == 0:64 ? 1:1 : 0:1;\n" +
                               "of_part1:1 = split(" + oldDest + ", 63, 63) != split(" + source + ", 63, 63) ? 1:1 : 0:1;\n" +
                               "of_part2:1 = split(" + source + ", 63, 63) == split(" + dest + ", 63, 63) ? 1:1 : 0:1;\n" +
                               "of:1 = of_part1:1 & of_part2:1;\n" +
                               "cf:1 = " + source + " > " + oldDest + " ? 1:1 : 0:1;\n" +
                               "sf:1 = split(" + dest + ", 63, 63);\n")

    return dslparse.dslToAst(tempString)


def ConvertAddq(x) :
    source, dest, oldDest, addr, tempString = SetupOperand64Bit(x)
    tempString = tempString + (oldDest + " = " + dest + ";\n" +
                               dest + " = " + dest + " + " + source + ";\n" +
                               SaveToOperand64Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + ("zf:1 = " + dest + " == 0:64 ? 1:1 : 0:1;" +
                               "cf_part1:1 = " + dest + " < " + oldDest + " ? 1:1 : 0:1;\n" +
                               "cf_part2:1 = " + dest + " < " + source + " ? 1:1 : 0:1;\n" +
                               "cf:1 = cf_part1:1 | cf_part2:1;\n" +
                               "of_part1:1 = split(" + oldDest + ", 63, 63) == split(" + source + ", 63, 63) ? 1:1 : 0:1;\n" +
                               "of_part2:1 = split(" + source + ", 63, 63) != split(" + dest + ", 63, 63) ? 1:1 : 0:1;\n" +
                               "of:1 = of_part1:1 & of_part2:1;\n" +
                               "sf:1 = split(" + dest + ", 63, 63);\n")
    return addqAstdslparse.dslToAst(tempString)


def ConvertAdcq(x) :
    source, dest, oldDest, addr, tempString = SetupOperand64Bit(x)
    tempString = tempString + (oldDest + " = " + dest + ";\n" +
                               dest + " = " + dest + " + " + source + " + zeroext(cf:1, 63);\n" +
                               SaveToOperand64Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + ("zf:1 = " + dest + " == 0:64 ? 1:1 : 0:1;" +
                               "cf_part1:1 = " + dest + " < " + oldDest + " ? 1:1 : 0:1;\n" +
                               "cf_part2:1 = " + dest + " < " + source + " ? 1:1 : 0:1;\n" +
                               "cf:1 = cf_part1:1 | cf_part2:1;\n" +
                               "of_part1:1 = split(" + oldDest + ", 63, 63) == split(" + source + ", 63, 63) ? 1:1 : 0:1;\n" +
                               "of_part2:1 = split(" + source + ", 63, 63) != split(" + dest + ", 63, 63) ? 1:1 : 0:1;\n" +
                               "of:1 = of_part1:1 & of_part2:1;\n" +
                               "sf:1 = split(" + dest + ", 63, 63);\n")
    return addqAstdslparse.dslToAst(tempString)


def ConvertAndq(x) :
    source, dest, oldDest, addr, tempString = SetupOperand64Bit(x)
    tempString = tempString + (dest + " = " + dest + " & " + source + ";\n" +
                               SaveToOperand64Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + ("zf:1 = " + dest + " == 0:64 ? 1:1 : 0:1;\n" +
                               "cf:1 = 0:1;\n" +
                               "of:1 = 0:1;\n" +
                               "sf:1 = split(" + dest + ", 63, 63);\n")
    return dslparse.dslToAst(tempString)


def ConvertXorq(x) :
    source, dest, oldDest, addr, tempString = SetupOperand64Bit(x)
    tempString = tempString + (dest + " = " + dest + " ^ " + source + ";\n" +
                               SaveToOperand64Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + ("zf:1 = " + dest + " == 0:64 ? 1:1 : 0:1;\n" +
                               "cf:1 = 0:1;\n" +
                               "of:1 = 0:1;\n" +
                               "sf:1 = split(" + dest + ", 63, 63);\n")
    return dslparse.dslToAst(tempString)


def ConvertLeaq(x) :
    if IsMemory(x[1]) and Is64Register(x[2]) :
        dest = x[2] + ":64"
        addr = CalculateAddress(x[1])
        dest32 = Get32BitRepFromRegister(x[2])[0]
        
        tempString = (dest + " = " + addr + ";\n" +
                      dest32 + " = " + "split(" + dest + ", 0, 31);\n")
        return dslparse.dslToAst(tempString)
    else : sys.exit("Convertleaq operand error: %s" % (x))


def ConvertCmpq(x) :
    temp = "tempCmpl64"
    source, dest, oldDest, addr, tempString = SetupOperand64Bit(x)
    tempString = tempString + temp + " = " + dest + " - " + source + ";\n"
            
    # Add flags
    tempString = tempString + ("zf:1 = " + temp + " == 0:64 ? 1:1 : 0:1;\n" +
                               "of_part1:1 = split(" + dest + ", 63, 63) != split(" + source + ", 63, 63) ? 1:1 : 0:1;\n" +
                               "of_part2:1 = split(" + source + ", 63, 63) == split(" + temp + ", 63, 63) ? 1:1 : 0:1;\n" +
                               "of:1 = of_part1:1 & of_part2:1;\n" +
                               "cf:1 = " + source + " > " + dest + " ? 1:1 : 0:1;\n" +
                               "sf:1 = split(" + temp + ", 63, 63);\n")
    
    return dslparse.dslToAst(tempString)

def ConvertShrq(x) :
    source, dest, oldDest, addr, tempString = SetupOperandForShifts64Bit(x)
    tempString = tempString + (oldDest + " = " + dest + ";\n" +
                               dest + " = " + dest + " >> " + source + ";\n" +
                               SaveToOperandForShifts64Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + "cf:1 = split(" + dest + ", 0, 0);\n"
    if int(x[1], 0) == 1 : tempString = tempString + "of:1 = split(" + oldDest + ", 63, 63);\n"
    else : tempString = tempString + "of:1 = builtin_undef;\n"
    tempString = tempString + ("zf:1 = " + dest + " == 0:64 ? 1:1 : 0:1;\n" +
                               "sf:1 = split(" + dest + ", 63, 63);\n")

    return dslparse.dslToAst(tempString)

def ConvertShlq(x) :
    source, dest, oldDest, addr, tempString = SetupOperandForShifts64Bit(x)
    tempString = tempString + (oldDest + " = " + dest + ";\n" + \
                               dest + " = " + dest + " << " + source + ";\n" +
                               SaveToOperandForShifts64Bit(x, source, dest, oldDest, addr))

    # Add flags
    tempString = tempString + "cf:1 = split(" + dest + ", 63, 63);\n"
    if int(x[1], 0) == 1 : tempString = tempString + "of:1 = split(" + oldDest + ", 63, 63);\n"
    else : tempString = tempString + "of:1 = builtin_undef;\n"
    tempString = tempString + ("zf:1 = " + dest + " == 0:64 ? 1:1 : 0:1;\n" +
                               "sf:1 = split(" + dest + ", 63, 63);\n")

    return dslparse.dslToAst(tempString)

    
def ConvertMovd(x) :
    tempString = ""
    # Movd xmm, 32-bit reg
    if Is128Register(x[1]) and Is32Register(x[2]) :
        source = [x[1] + "_0", x[1] + "_1", x[1] + "_2", x[1] + "_3"]
        dest = x[2]
        dest64 = Get64BitRepFromRegister(x[2])[0]
        tempString = (dest + " = " + source[0] + ";\n" +
                      dest64 + " = " + "zeroext(" + dest + ", 32);\n")
            
    # Movd xmm, 32-bit memory
    elif Is128Register(x[1]) and IsMemory(x[2]) :
        source = [x[1] + "_0", x[1] + "_1", x[1] + "_2", x[1] + "_3"]
        addr = CalculateAddress(x[2])
        tempString = StoreToMemoryString(addr, 4, source[0])
        
    # Movd 32-bit reg, xmm
    elif Is32Register(x[1]) and Is128Register(x[2]) :
        source = x[1]
        dest = [x[2] + "_0", x[2] + "_1", x[2] + "_2", x[2] + "_3"]
        tempString = (dest[0] + " = " + source + ";\n" +
                      dest[1] + " = 0;\n" +
                      dest[2] + " = 0;\n" +
                      dest[3] + " = 0;\n")
            
    # Movd 32-bit mem, xmm
    elif IsMemory(x[1]) and Is128Register(x[2]) :
        addr = CalculateAddress(x[1])
        dest = [x[2] + "_0", x[2] + "_1", x[2] + "_2", x[2] + "_3"]
        tempString = (LoadFromMemoryString(addr, 4, dest[0]) +
                      dest[1] + " = 0;\n" +
                      dest[2] + " = 0;\n" +
                      dest[3] + " = 0;\n")
    else : sys.exit("ConvertMovd operand error: %s" % (x))
        
    return dslparse.dslToAst(tempString)

def ConvertMovq(x) :
    tempString = ""
    # 64-bit reg to 64-bit reg
    if (isImmediate(x[1]) or Is64Register(x[1])) and Is64Register(x[2]) :
        source = x[1] + ":64"
        dest = x[2] + ":64"
        dest32 = Get32BitRepFromRegister(x[2])[0]
        tempString = (dest + " = " + source + ";\n" +
                      dest32 + " = " + "split(" + dest + ", 0, 31);\n")
        
    # 64-bit reg to 64-bit mem
    elif (isImmediate(x[1]) or Is64Register(x[1])) and IsMemory(x[2]) :
        source = x[1] + ":64"
        addr = CalculateAddress(x[2])
        tempString = StoreToMemoryString(addr, 8, source)

    # 64-bit mem to 64-bit reg
    elif IsMemory(x[1]) and Is64Register(x[2]) :
        addr = CalculateAddress(x[1])
        dest = x[2] + ":64"
        dest32 = Get32BitRepFromRegister(x[2])[0]
        tempString = (LoadFromMemoryString(addr, 8, dest) +
                      dest32 + " = split(" + dest + ", 0, 31);\n")

    # 128-bit reg to 64-bit reg
    elif Is128Register(x[1]) and Is64Register(x[2]) :
        source = [x[1] + "_0", x[1] + "_1", x[1] + "_2", x[1] + "_3"]
        dest = x[2] + ":64"
        dest32 = Get32BitRepFromRegister(x[2])[0]
        tempString = (dest + " = merge(" + source[1] + ", " + source[0] + ");\n" +
                      dest32 + " = split(" + dest + ", 0, 31);\n")
            
    # 64-bit reg to 128-bit reg
    elif Is64Register(x[1]) and Is128Register(x[2]) :
        source = x[1] + ":64"
        dest = [x[2] + "_0", x[2] + "_1", x[2] + "_2", x[2] + "_3"]
        tempString = (dest[0] + " = split(" + source + ", 0, 31);\n" +
                      dest[1] + " = split(" + source + ", 32, 63);\n" +
                      dest[2] + " = 0;\n" +
                      dest[3] + " = 0;\n")
    else : sys.exit("ConvertMovd operand error: %s" % (x))

    return dslparse.dslToAst(tempString)

def ConvertDefault(x) :
    sys.exit("Please implement Convert for: %s" % (x))

def ConvertToDsl(x86Insts) :
    retList = []
    for x86I in x86Insts :
        convFunc = convertSwitcher.get(x86I[0], ConvertDefault)
        insts = convFunc(x86I)
        retList.extend(insts)
    return retList

convertSwitcher = {
    "pushq" : ConvertPushq,
    "popq" : ConvertPopq,
    "movl" : ConvertMovl,
    "movd" : ConvertMovd,
    "movq" : ConvertMovq,
    "addl" : ConvertAddl,
    "adcl" : ConvertAdcl,
    "cmpl" : ConvertCmpl,
    "cmpq" : ConvertCmpq,
    "decl" : ConvertDecl,
    "xorl" : ConvertXorl,
    "xorq" : ConvertXorq,
    "andl" : ConvertAndl,
    "shrl" : ConvertShrl,
    "shll" : ConvertShll,
    "shrq" : ConvertShrq,
    "shlq" : ConvertShlq,
    "rorl" : ConvertRorl,
    "roll" : ConvertRoll,
    "subq" : ConvertSubq,
    "sbbq" : ConvertSbbq,
    "leaq" : ConvertLeaq,
    "subl" : ConvertSubl,
    "sbbl" : ConvertSbbl,
    "movzbl" : ConvertMovzbl,
    "andq" : ConvertAndq,
    "addq" : ConvertAddq,
    "adcq" : ConvertAdcq,
    "bswapl" : ConvertBswapl,
    "cmpb" : ConvertCmpb,
    "cmovzl" : ConvertCmovzl,
    "cmovnzl" : ConvertCmovnzl,
    "cmovel" : ConvertCmovel,
    "cmovnel" : ConvertCmovnel,
    "cmovgel" : ConvertCmovgel,
    "cmovll" : ConvertCmovll,
    "cmovlel" : ConvertCmovlel,
    "cmovgl" : ConvertCmovgl,
    "cmovncl" : ConvertCmovncl,
    "cmovnol" : ConvertCmovnol
}
