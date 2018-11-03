from x86todslHelper import *
import dslinstructions
import dslparse
import config
import sys

def ConvertRorl(x) :
    # 32 bit rotate right operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = " + dest + ":32 >>> " + source + ":32;\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = " + "zeroext(" + dest + ":32, 32);\n"
    
    # cf : The most significant bit of the result
    tempString = tempString + "cf:1 = split(" + dest + ", 31, 31);\n"
    
    # of : if source == 1, then of = the xor of the two most significant bits.
    sourceVal = int(x[1], 0)
    if sourceVal == 1 :
        tempString = tempString + "of:1 = split(" + dest + ", 31, 31) ^ split(" + dest + ", 30, 30);\n"
    else :
        tempString = tempString + "of:1 = builtin_undef;\n"
        
    rorAst = dslparse.dslToAst(tempString)
    return rorAst

def ConvertRoll(x) :
    # 32 bit rotate left operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = " + dest + " <<< " + source + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = " + "zeroext(" + dest + ", 32);\n"

    # cf : The least significant bit of the result
    tempString = tempString + "cf:1 = split(" + dest + ", 0, 0);\n"
    # of : if source == 1, then of = the xor of the most significant bit and cf
    sourceVal = int(x[1], 0)
    if sourceVal == 1 :
        tempString = tempString + "of:1 = split(" + dest + ", 31, 31) ^ cf:1;\n"
    else :
        tempString = tempString + "of:1 = builtin_undef;\n"
    
    rolAst = dslparse.dslToAst(tempString)
    return rolAst

def ConvertAddl(x) :
    # 32 bit addition operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + "oldDest = " + dest + ";\n"
    tempString = tempString + dest + " = " + dest + " + " + source + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = " + "zeroext(" + dest + ", 32);\n"

    # zf : 1 if the result is 0?
    tempString = tempString + "zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n"
    # cf : (dest < oldDest) or (dest < source)
    tempString = tempString + "cf_part1:1 = " + dest + " < oldDest ? 1:1 : 0:1;\n"
    tempString = tempString + "cf_part2:1 = " + dest + " < " + source + " ? 1:1 : 0:1;\n"
    tempString = tempString + "cf:1 = cf_part1:1 | cf_part2:1;\n"
    # of : of:1 = (MSB(oldDest) == MSB(source)) and (MSB(source) != MSB(dest))
    tempString = tempString + "of_part1:1 = split(oldDest, 31, 31) == split(" + source + ", 31, 31) ? 1:1 : 0:1;\n"
    tempString = tempString + "of_part2:1 = split(" + source + ", 31, 31) != split(" + dest + ", 31, 31) ? 1:1 : 0:1;\n"
    tempString = tempString + "of:1 = of_part1:1 & of_part2:1;\n"
    # sf : sign bit of the result
    tempString = tempString + "sf:1 = split(" + dest + ", 31, 31);\n"

    addAst = dslparse.dslToAst(tempString)
    return addAst

def ConvertAdcl(x) :
    # 32 bit addition operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + "oldDest = " + dest + ";\n"
    tempString = tempString + dest + " = " + dest + " + " + source + " + zeroext(cf:1, 31)" + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = " + "zeroext(" + dest + ", 32);\n"

    # zf : 1 if the result is 0?
    tempString = tempString + "zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n"
    # cf : (dest < oldDest) or (dest < source)
    tempString = tempString + "cf_part1:1 = " + dest + " < oldDest ? 1:1 : 0:1;\n"
    tempString = tempString + "cf_part2:1 = " + dest + " < " + source + " ? 1:1 : 0:1;\n"
    tempString = tempString + "cf:1 = cf_part1:1 | cf_part2:1;\n"
    # of : of:1 = (MSB(oldDest) == MSB(source)) and (MSB(source) != MSB(dest))
    tempString = tempString + "of_part1:1 = split(oldDest, 31, 31) == split(" + source + ", 31, 31) ? 1:1 : 0:1;\n"
    tempString = tempString + "of_part2:1 = split(" + source + ", 31, 31) != split(" + dest + ", 31, 31) ? 1:1 : 0:1;\n"
    tempString = tempString + "of:1 = of_part1:1 & of_part2:1;\n"
    # sf : sign bit of the result
    tempString = tempString + "sf:1 = split(" + dest + ", 31, 31);\n"

    addAst = dslparse.dslToAst(tempString)
    return addAst


def ConvertShrl(x) :
    # 32 bit shift right operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + "oldDest = " + dest + ";\n"
    tempString = tempString + dest + " = " + dest + " >> " + source + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = " + "zeroext(" + dest + ", 32);\n"

    # cf : least significant bit of destination
    tempString = tempString + "cf:1 = split(oldDest, " + str(int(source, 0) - 1) + ", " + str(int(source, 0) - 1) + ");\n"
    # of : if source == 1, most significant bit of old destination
    sourceVal = int(x[1], 0)
    if sourceVal == 1 :
        tempString = tempString + "of:1 = split(oldDest, 31, 31);\n"
    else :
        tempString = tempString + "of:1 = builtin_undef;\n"
        
    shrAst = dslparse.dslToAst(tempString)
    return shrAst

def ConvertXorl(x) :
    # 32 bit xor operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = " + dest + " ^ " + source + ";"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = " + "zeroext(" + dest + ", 32);\n"

    # zf : dest == 0
    tempString = tempString + "zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n"
    # cf : 0
    tempString = tempString + "cf:1 = 0:1;\n"
    # of : 0
    tempString = tempString + "of:1 = 0:1;\n"
    # sf : most significant bit of dest
    tempString = tempString + "sf:1 = split(" + dest + ", 31, 31);\n"
        
    xorAst = dslparse.dslToAst(tempString)
    return xorAst

def ConvertAndl(x) :
    # 32 bit and operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = " + dest + " & " + source + ";"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = " + "zeroext(" + dest + ", 32);\n"

    # zf : dest == 0
    tempString = tempString + "zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n"
    # cf : 0
    tempString = tempString + "cf:1 = 0:1;\n"
    # of : 0
    tempString = tempString + "of:1 = 0:1;\n"
    # sf : most significant bit of dest
    tempString = tempString + "sf:1 = split(" + dest + ", 31, 31);\n"
        
    andAst = dslparse.dslToAst(tempString)
    return andAst
        
def ConvertMovl(x) :
    # 32 bit mov operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = " + source + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    movAst = dslparse.dslToAst(tempString)
    return movAst

def ConvertCmovzl(x) :
    # 32 bit mov if zf == 1 operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = zf:1 == 1:1 ? " + source + " : " + dest + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    movAst = dslparse.dslToAst(tempString)
    return movAst

def ConvertCmovncl(x) :
    # 32 bit mov if zf == 1 operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = cf:1 == 0:1 ? " + source + " : " + dest + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    movAst = dslparse.dslToAst(tempString)
    return movAst

def ConvertCmovnol(x) :
    # 32 bit mov if zf == 1 operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = of:1 == 0:1 ? " + source + " : " + dest + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    movAst = dslparse.dslToAst(tempString)
    return movAst

def ConvertCmovol(x) :
    # 32 bit mov if of == 1 operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = of:1 == 1:1 ? " + source + " : " + dest + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    movAst = dslparse.dslToAst(tempString)
    return movAst

def ConvertCmovnzl(x) :
    # 32 bit mov if zf == 0 operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = zf:1 == 0:1 ? " + source + " : " + dest + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    movAst = dslparse.dslToAst(tempString)
    return movAst

def ConvertCmovel(x) :
    # 32 bit mov if zf == 1 operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = zf:1 == 1:1 ? " + source + " : " + dest + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    movAst = dslparse.dslToAst(tempString)
    return movAst

def ConvertCmovnel(x) :
    # 32 bit mov if zf == 0 operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = zf:1 == 0:1 ? " + source + " : " + dest + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    movAst = dslparse.dslToAst(tempString)
    return movAst

def ConvertCmovgel(x) :
    # 32 bit mov if sf == of operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = sf:1 == of:1 ? " + source + " : " + dest + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    movAst = dslparse.dslToAst(tempString)
    return movAst

def ConvertCmovll(x) :
    # 32 bit mov if sf != of of operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = sf:1 != of:1 ? " + source + " : " + dest + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    movAst = dslparse.dslToAst(tempString)
    return movAst

def ConvertCmovlel(x) :
    # 32 bit mov if zf = 1 or sf != of of operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = ((sf:1 ^ of:1) | zf:1) == 1:1 ? " + source + " : " + dest + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    movAst = dslparse.dslToAst(tempString)
    return movAst

def ConvertCmovgl(x) :
    # 32 bit mov if zf = 0 and sf == of of operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + dest + " = (!(sf:1 ^ of:1) & !zf:1) == 1:1 ? " + source + " : " + dest + ";\n"

    if config.Is64BitArch() and Is32Register(x[2]) :
        dest64 = GetRegister(x[2], 64)[0]
        tempString = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    movAst = dslparse.dslToAst(tempString)
    return movAst

def ConvertMovzbl(x) :
    # 1 byte -> 8 byte zero extend.
    destList, tempString = ConvertOperand(x[2])
    dest = destList[0]

    if isinstance(x[1], pp.ParseResults) or isinstance(x[1], list) :
        base = x[1][1]
        if base in reg64Rev :
            base = base + ":64"
        taddr = base
        if len(x[1]) == 4 :
            hasIndex = True
            index = x[1][2]
            if index in reg64Rev :
                index = index + ":64"
            multiplier = int(x[1][3])
            if multiplier == 1 :
                taddr = taddr + " + " + index
            elif multiplier == 2 :
                taddr = taddr + " + (" + index + " << 1:64) "
            elif multiplier == 4 :
                taddr = taddr + " + (" + index + " << 2:64) "
            elif multiplier == 8 :
                taddr = taddr + " + (" + index + " << 3:64) "

        offset = 0 if x[1][0] == "OFFSET" else int(x[1][0])
        if offset % 4 == 0 :
            # Then we have no problem.
            if not offset == 0 :
                taddr = taddr + " + " + str(offset)
            tempString = tempString + "movzbltemparray = mem[" + taddr + "]\n;"
            tempString = tempString + "movzblmemval:8 = split(movzbltemparray, 0, 7)\n;"
            source = "movzblmemval:8"
        else :
            # We gotta start thinking about offset memory loads.
            newoffset = int(offset / 4)
            offsetrem = offset % 4
            taddr = taddr if newoffset == 0 else (taddr + " + " + str(newoffset))
            tempString = tempString + "movzbltemparray = mem[" + taddr + "]\n;"
            tempString = tempString + "movzblmemval:8 = split(movzbltemparray, " + str(offsetrem * 8) + ", " + str((offsetrem + 1) * 8 - 1) + ")\n;"
            source = "movzblmemval:8"
    else :
        source = x[1] + ":8"
        if x[1] in reg8lowRev :
            index = reg8lowRev[x[1]]
            base = reg32[index]
            tempString = tempString + source + " = split(" + base + ", 0, 7);\n"
        elif x[1] in reg8highRev :
            index = reg8highRev[x[1]]
            base = reg32[index]
            tempString = tempString + source + " = split(" + base + ", 8, 15);\n"

    tempString = tempString + dest + " = zeroext(" + source + ", 24);\n"

    if config.Is64BitArch() :
        dest64 = GetRegister(dest, 64)[0]
        tempString = tempString + dest64 + " = zeroext(" + source + ", 56);\n"
    
    movzblAst = dslparse.dslToAst(tempString)
    return movzblAst

def ConvertCmpl(x) :
    # Right side - left side.
    # 32 bit cmp operation
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    tempString = tempString + "temp = " + dest + " - " + source + ";\n"
    # zf
    tempString = tempString + "zf:1 = temp == 0 ? 1:1 : 0:1;\n"
    # of : (left side sign bit) != (right side sign bit) and (right side sign bit) == (result sign bit)
    tempString = tempString + "of_part1:1 = split(" + source + ", 31, 31) != split(" + dest + ", 31, 31) ? 1:1 : 0:1;\n"
    tempString = tempString + "of_part2:1 = split(" + dest + ", 31, 31) == split(temp, 31, 31) ? 1:1 : 0:1;\n"
    tempString = tempString + "of:1 = of_part1:1 & of_part2:1;\n"
    # cf : most significant bit requires carry if source is greater than dest.
    tempString = tempString + "cf:1 = " + source + " > " + dest + " ? 1:1 : 0:1;\n"
    # sf
    tempString = tempString + "sf:1 = split(temp, 31, 31);\n"

    cmpAst = dslparse.dslToAst(tempString)
    return cmpAst

def ConvertCmpq(x) :
    # 64 bit compare
    sourceList, tempString = ConvertOperand(x[1], "", 64)
    destList, tempString = ConvertOperand(x[2], tempString, 64)

    if len(sourceList) ==  1 :
        # It's a register
        source = sourceList[0]
    elif len(sourceList) == 2 :
        # It's a memory operation
        tempString = tempString + "tempSourceOp:64 = merge(" + sourceList[1] + ", " + sourceList[0] + ");\n"
        source = "tempSourceOp:64"
    else :
        sys.exit("ConvertCmpq. Encountered an unexpected operand: " + x[1])

    if len(destList) == 1 :
        # It's a register
        dest = destList[0]
    elif len(destList) == 2 :
        # It's a memory operation
        tempString = tempString + "tempDestOp:64 = merge(" + destList[1] + ", " + destList[0] + ");\n"
        dest = "tempDestOp:64"
    else :
        sys.exit("ConvertCmpq. Encountered an unexpected operand: " + x[2])

    tempString = tempString + "temp:64 = " + dest + " - " + source + ";\n"
    # zf
    tempString = tempString + "zf:1 = temp:64 == 0:64 ? 1:1 : 0:1;\n"
    # of : (left side sign bit) != (right side sign bit) and (right side sign bit) == (result sign bit)
    tempString = tempString + "of_part1:1 = split(" + source + ", 63, 63) != split(" + dest + ", 63, 63) ? 1:1 : 0:1;\n"
    tempString = tempString + "of_part2:1 = split(" + dest + ", 63, 63) == split(temp, 63, 63) ? 1:1 : 0:1;\n"
    tempString = tempString + "of:1 = of_part1:1 & of_part2:1;\n"
    # cf
    tempString = tempString + "cf:1 = " + source + " > " + dest + " ? 1:1 : 0:1;\n"
    # sf
    tempString = tempString + "sf:1 = split(temp, 63, 63);\n"
    
    cmpAst = dslparse.dslToAst(tempString)
    return cmpAst

def ConvertCmpb(x) :
    # Comparing a single byte.
    # For time's sake, we will only implement it for ['cmpb', '0', ['3', 'base reg']]. Make sure we say error if not.
    if (not isImmediate(x[1])) or (isinstance(x[2], str)) or (len(x[2]) != 2) :
        sys.exit("Implementation of Cmpb is incomplete. Does not support " + str(x))

    source = x[1]
    offset = 0
    byte_index = 0
    if x[2][0] != "OFFSET" :
        offset = int(x[2][0]) // int(4)
        byte_index = int(x[2][0]) % int(4)

    destOperand = "split(mem[" + x[2][1] + ":64 + " + str(offset) + ":64], " + str(byte_index * 8) + ", " + str(byte_index * 8 + 7) + ")"
    tempString = "tempDest:8 = " + destOperand + ";\n"
    tempString = tempString + "temp:8 = tempDest:8" + " - " + source + ":8;\n"
    tempString = tempString + "zf:1 = temp:8 == 0:8 ? 1:1 : 0:1;\n"
    tempString = tempString + "of_part1:1 = split(" + source + ":8, 7, 7) != split(tempDest:8, 7, 7) ? 1:1 : 0:1;\n"
    tempString = tempString + "of_part2:1 = split(tempDest:8, 7, 7) == split(temp:8, 7, 7) ? 1:1 : 0:1;\n"
    tempString = tempString + "of:1 = of_part1:1 & of_part2:1;\n"
    tempString = tempString + "cf:1 = " + source + ":8 > tempDest:8 ? 1:1 : 0:1;\n"
    tempString = tempString + "sf:1 = split(temp:8, 7, 7);\n"

    cmpbAst = dslparse.dslToAst(tempString)
    return cmpbAst

def ConvertDecl(x) :
    # 32 bit dec operation
    tempString = ""
    
    destList, tempString = ConvertOperand(x[1], tempString)
    dest = destList[0]
    tempString = tempString + "tempDest = " + dest + ";\n"
    tempString = tempString + dest + " = " + dest + " - 1;\n"

    # zf : dest == 0
    tempString = tempString + "zf:1 = " + dest + " == 0 ? 1:1 : 0:1;\n"
    # cf : if old dest
    tempString = tempString + "cf:1 = 1 > tempDest ? 1:1 : 0:1;\n"
    # of
    tempString = tempString + "of_part1:1 = 0 != split(tempDest, 31, 31) ? 1:1 : 0:1;\n"
    tempString = tempString + "of_part2:1 = split(tempDest, 31, 31) == split(" + dest + ", 31, 31) ? 1:1 : 0:1;\n"
    tempString = tempString + "of:1 = of_part1:1 & of_part2:1;\n"
    # sf
    tempString = tempString + "sf:1 = split(" + dest + ", 31, 31);\n"

    if config.Is64BitArch() and Is32Register(x[1]) :
        dest64 = GetRegister(x[1], 64)[0]
        tempString = tempString + dest64 + " = " + "zeroext(" + dest + ", 32);\n"
    declAst = dslparse.dslToAst(tempString)
    return declAst

##### 64 bit operation

def ConvertShrq(x) :
    # 64 bit shr
    # Source : DNE or immediate
    # Dest : 64-bit register or memory
    if len(x) == 1 :
        # There is no source, only dest
        sop = "1"
        dop = x[1]
    else :
        sop = x[1]
        dop = x[2]
    
    destList = []
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destName = ""
    
    if IsMemory(dop) :
        destList, blah = ConvertOperand(dop, "", 32, 64)
        tempString = tempString + "tempD:64 = merge(" + destList[1] + ", " + destList[0] + ");\n"
        destName = "tempD:64"
    else :
        destList, blah = ConvertOperand(dop, "", 64)
        destName = destList[0]

    tempString = tempString + "oldTempDestShrq:64 = " + destName + ";\n"
    tempString = tempString + destName + " = " + destName + " >> " + source + ":64;\n"
    destList, blah = ConvertOperand(dop, "", 32, 64)
    tempString = tempString + destList[0] + " = split(" + destName + ", 0, 31);\n"
    tempString = tempString + destList[1] + " = split(" + destName + ", 32, 63);\n"

    # cf : least significant bit of destination
    tempString = tempString + "cf:1 = split(" + destName + ", 0, 0);\n"
    # of : if source == 1, most significant bit of old destination
    sourceVal = int(x[1], 0)
    if sourceVal == 1 :
        tempString = tempString + "of:1 = split(oldTempDestShrq:64, 63, 63);\n"
    else :
        tempString = tempString + "of:1 = builtin_undef;\n"
    
    shrqAst = dslparse.dslToAst(tempString)
    return shrqAst

def ConvertShlq(x) :
    # 64 bit shr
    # Source : DNE or immediate
    # Dest : 64-bit register or memory
    if len(x) == 1 :
        # There is no source, only dest
        sop = "1"
        dop = x[1]
    else :
        sop = x[1]
        dop = x[2]
    
    destList = []
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destName = ""
    
    if IsMemory(dop) :
        destList, blah = ConvertOperand(dop, "", 32, 64)
        tempString = tempString + "tempD:64 = merge(" + destList[1] + ", " + destList[0] + ");\n"
        destName = "tempD:64"
    else :
        destList, blah = ConvertOperand(dop, "", 64)
        destName = destList[0]

    tempString = tempString + "oldTempDestShlq:64 = " + destName + ";\n"
    tempString = tempString + destName + " = " + destName + " << " + source + ":64;\n"
    destList, blah = ConvertOperand(dop, "", 32, 64)
    tempString = tempString + destList[0] + " = split(" + destName + ", 0, 31);\n"
    tempString = tempString + destList[1] + " = split(" + destName + ", 32, 63);\n"

    # cf : most significant bit of destination
    tempString = tempString + "cf:1 = split(" + destName + ", 63, 63);\n"
    # of : if source == 1, most significant bit of old destination
    sourceVal = int(x[1], 0)
    if sourceVal == 1 :
        tempString = tempString + "of:1 = split(oldTempDestShlq:64, 63, 63) ^ cf:1;\n"
    else :
        tempString = tempString + "of:1 = builtin_undef;\n"
    
    shrqAst = dslparse.dslToAst(tempString)
    return shrqAst

def ConvertSubq(x) :
    # 64 bit sub
    sourceList, tempString = ConvertOperand(x[1])
    destList, tempString = ConvertOperand(x[2], tempString)
    ld = destList[0]
    hd = destList[1]
    tempString = "oldDestSubq:64 = " + x[2] + ":64;\n"
    tempString = tempString + x[2] + ":64 = " + x[2] + ":64 - " + sourceList[0] + ":64;\n" \
               + ld + " = split(" + x[2] + ":64, 0, 31);\n" \
               + hd + " = split(" + x[2] + ":64, 32, 63);\n"

    # zf
    tempString = tempString + "zf:1 = " + x[2] + ":64 == 0:64 ? 1:1 : 0:1;"
    # of : (left side sign bit) != (right side sign bit) and (right side sign bit) == (result sign bit)
    tempString = tempString + "of_part1:1 = split(" + sourceList[0] + ":64, 63, 63) != split(oldDestSubq:64, 63, 63) ? 1:1 : 0:1;\n"
    tempString = tempString + "of_part2:1 = split(oldDestSubq:64, 63, 63) == split(" + x[2] + ":64, 63, 63) ? 1:1 : 0:1;\n"
    tempString = tempString + "of:1 = of_part1:1 & of_part2:1;\n"
    # cf
    tempString = tempString + "cf:1 = " + sourceList[0] + ":64 > oldDestSubq:64 ? 1:1 : 0:1;\n"
    # sf
    tempString = tempString + "sf:1 = split(" + x[2] + ":64, 63, 63);\n"

    shrqAst = dslparse.dslToAst(tempString)
    return shrqAst

def ConvertAddq(x) :
    # 64 bit sub
    sourceList, tempString = ConvertOperand(x[1])
    destList, tempString = ConvertOperand(x[2], tempString)
    ld = destList[0]
    hd = destList[1]
    tempString = tempString + "tempDestAddq:64 = " + x[2] + ":64;\n"
    tempString = tempString + x[2] + ":64 = " + x[2] + ":64 + " + sourceList[0] + ":64;\n" \
               + ld + " = split(" + x[2] + ":64, 0, 31);\n" \
               + hd + " = split(" + x[2] + ":64, 32, 63);\n"

    # zf : 1 if the result is 0?
    tempString = tempString + "zf:1 = " + x[2] + ":64 == 0:64 ? 1:1 : 0:1;"
    # cf : (dest < tempDestAddq) or (dest < source)
    tempString = tempString + "cf_part1:1 = " + x[2] + ":64 < tempDestAddq:64 ? 1:1 : 0:1;\n"
    tempString = tempString + "cf_part2:1 = " + x[2] + ":64 < " + sourceList[0] + ":64 ? 1:1 : 0:1;\n"
    tempString = tempString + "cf:1 = cf_part1:1 | cf_part2:1;\n"
    # of : of:1 = (MSB(tempDestAddq) == MSB(source)) and (MSB(source) != MSB(dest))
    tempString = tempString + "of_part1:1 = split(tempDestAddq:64, 63, 63) == split(" + sourceList[0] + ":64, 63, 63) ? 1:1 : 0:1;\n"
    tempString = tempString + "of_part2:1 = split(" + sourceList[0] + ":64, 63, 63) != split(" + x[2] + ":64, 63, 63) ? 1:1 : 0:1;\n"
    tempString = tempString + "of:1 = of_part1:1 & of_part2:1;\n"
    # sf : sign bit of the result
    tempString = tempString + "sf:1 = split(" + x[2] + ":64, 63, 63);\n"

    shrqAst = dslparse.dslToAst(tempString)
    return shrqAst

def ConvertAndq(x) :
    # 64 bit And
    sourceList, tempString = ConvertOperand(x[1])
    destList, tempString = ConvertOperand(x[2], tempString)
    ld = destList[0]
    hd = destList[1]
    tempString = tempString + x[2] + ":64 = merge(" + hd + ", " + ld + ");\n" \
               + x[2] + ":64 = " + x[2] + ":64 & " + sourceList[0] + ":64;\n" \
               + ld + " = split(" + x[2] + ":64, 0, 31);\n" \
               + hd + " = split(" + x[2] + ":64, 32, 63);\n"

    # zf : dest == 0
    tempString = tempString + "zf:1 = " + x[2] + ":64 == 0:64 ? 1:1 : 0:1;\n"
    # cf : 0
    tempString = tempString + "cf:1 = 0:1;\n"
    # of : 0
    tempString = tempString + "of:1 = 0:1;\n"
    # sf : most significant bit of dest
    tempString = tempString + "sf:1 = split(" + x[2] + ":64, 63, 63);\n"

    shrqAst = dslparse.dslToAst(tempString)
    
    return shrqAst


def ConvertSubl(x) :
    # 32 bit subtract.
    sourceList, tempString = ConvertOperand(x[1])
    source = sourceList[0]
    destList, tempString = ConvertOperand(x[2], tempString)
    dest = destList[0]
    sl = sourceList[0]
    dl = destList[0]

    tempString = tempString + "tempDestSubl = " + dl + ";\n"
    tempString = tempString + dl + " = " + dl + " - " + sl + ";\n"

    if config.Is64BitArch() :
        dl64 = GetRegister(dl, 64)[0]
        tempString = tempString + dl64 + " = zeroext(" + dl + ", 32);\n"


    # zf
    tempString = tempString + "zf:1 = " + dl + " == 0 ? 1:1 : 0:1;\n"
    # of : (left side sign bit) != (right side sign bit) and (right side sign bit) == (result sign bit)
    tempString = tempString + "of_part1:1 = split(tempDestSubl, 31, 31) != split(" + sl + ", 31, 31) ? 1:1 : 0:1;\n"
    tempString = tempString + "of_part2:1 = split(" + sl + ", 31, 31) == split(" + dl + ", 31, 31) ? 1:1 : 0:1;\n"
    tempString = tempString + "of:1 = of_part1:1 & of_part2:1;\n"
    # cf : most significant bit requires carry if source is greater than old dest.
    tempString = tempString + "cf:1 = " + sl + " > tempDestSubl ? 1:1 : 0:1;\n"
    # sf
    tempString = tempString + "sf:1 = split(" + dl + ", 31, 31);\n"

    sublAst = dslparse.dslToAst(tempString)
    return sublAst

def ConvertBswapl(x) :
    # 32 bit subtract.
    assert(len(x) == 2)
    
    destList, tempString = ConvertOperand(x[1])
    dest = destList[0]
    dest64 = GetRegister(dest, 64)[0]
    
    tempString = tempString + dest + " = merge(split(" + dest + ", 0, 7), merge(split(" + dest + ", 8, 15), merge(split(" + dest + ", 16, 23), split(" + dest + ", 24, 31))));\n"

    if config.Is64BitArch() :
        dest64 = GetRegister(dest, 64)[0]
        tempStrig = tempString + dest64 + " = zeroext(" + dest + ", 32);\n"

    bswaplAst = dslparse.dslToAst(tempString)
    return bswaplAst

def ConvertLeaq(x) :
    # 64 bit load
    if len(x[1]) == 2 :
        source = x[1][1] + ":64"
        if x[1][0] != "OFFSET" :
            source = source + " + " + x[1][0] + ":64"
    elif len(x[1]) == 4 :
        source = x[1][1] + ":64"
        if x[1][0] != "OFFSET" :
            source = source + " + " + x[1][0] + ":64"
        if x[1][3] == "1" :
            source = source + " + " + x[1][2] + ":64" + ""
        elif x[1][3] == "2" :
            source = source + " + " + x[1][2] + ":64" + " << 1:64"
        elif x[1][3] == "4" :
            source = source + " + " + x[1][2] + ":64" + " << 2:64"
        elif x[1][3] == "8" :
            source = source + " + " + x[1][2] + ":64" + " << 3:64"
        else :
            sys.exit("Unexpected error." + str(x))
    else :
        sys.exit("We did not think of case when Leaq is not base(register). Please implement it." + str(x))
    
    destList, blah = ConvertOperand(x[2], "", 64)
    dest64 = destList[0]
    tempString = dest64 + " = " + source + ";\n"
    
    destList, blah = ConvertOperand(x[2])
    ld = destList[0]
    hd = destList[1]
    tempString = tempString + ld + " = split(" + dest64 + ", 0, 31);\n" \
               + hd + " = split(" + dest64 + ", 32, 63);\n"
    
    leaAst = dslparse.dslToAst(tempString)
    return leaAst

def ConvertMovd(x) :
    tempString = ""
    if x[2] in reg128Rev :
        # Moving lower 32bit of xmm to 32bit space
        sourceList, tempString = ConvertOperand(x[1], tempString)
        destList, tempString = ConvertOperand(x[2], tempString)
        tempString = tempString + destList[0] + " = " + sourceList[0] + ";\n"
    else :
        # Moving 32bit data to lower 32bit of xmm
        sourceList, tempString = ConvertOperand(x[1], tempString)
        destList, tempString = ConvertOperand(x[2], tempString)
        tempString = tempString + destList[0] + " = " + sourceList[0] + ";\n"

    movdAst = dslparse.dslToAst(tempString)
    return movdAst

def ConvertMovq(x) :
    # Moving lower 2 32-bit to somewhere.
    sop = x[1]
    dop = x[2]
    tempString = ""
    if Is128Register(sop) and Is128Register(dop) :
        sourceList, tempString = ConvertOperand(sop, tempString)
        destList, tempString = ConvertOperand(dop, tempString)
        tempString = tempString + destList[0] + " = " + sourceList[0] + ";\n"
        tempString = tempString + destList[1] + " = " + sourceList[1] + ";\n"
    elif Is128Register(sop) and IsMemory(dop) :
        sourceList, tempString = ConvertOperand(sop, tempString)
        destList, tempString = ConvertOperand(dop, tempString, 32, 64)
        tempString = tempString + destList[0] + " = " + sourceList[0] + ";\n"
        tempString = tempString + destList[1] + " = " + sourceList[1] + ";\n"
    elif Is64Register(sop) and IsMemory(dop) :
        sourceList, tempString = ConvertOperand(sop, tempString)
        destList, tempString = ConvertOperand(dop, tempString, 32, 64)
        tempString = tempString + sourceList[0] + " = " + "split(" + sop + ":64, 0, 31);\n"
        tempString = tempString + sourceList[1] + " = " + "split(" + sop + ":64, 32, 63);\n"
        tempString = tempString + destList[0] + " = " + sourceList[0] + ";\n"
        tempString = tempString + destList[1] + " = " + sourceList[1] + ";\n"
    elif IsMemory(sop) and Is128Register(dop) :
        sourceList, tempString = ConvertOperand(sop, tempString, 32, 64)
        destList, tempString = ConvertOperand(dop, tempString)
        tempString = tempString + destList[0] + " = " + sourceList[0] + ";\n"
        tempString = tempString + destList[1] + " = " + sourceList[1] + ";\n"
    elif IsMemory(sop) and Is64Register(dop) :
        sourceList, tempString = ConvertOperand(sop, tempString, 32, 64)
        destList, tempString = ConvertOperand(dop, tempString, 32, 64)
        tempString = tempString + destList[0] + " = " + sourceList[0] + ";\n"
        tempString = tempString + destList[1] + " = " + sourceList[1] + ";\n"
        dest64 = GetRegister(dop, 64)[0]
        tempString = tempString + dest64 + " = merge(" + destList[1] + ", " + destList[0] + ");\n"
    elif Is64Register(sop) and Is128Register(dop) :
        sourceList, tempString = ConvertOperand(sop, tempString)
        destList, tempString = ConvertOperand(dop, tempString)
        tempString = tempString + destList[0] + " = " + sourceList[0] + ";\n"
        tempString = tempString + destList[1] + " = " + sourceList[1] + ";\n"
    elif Is128Register(sop) and Is64Register(dop) :
        sourceList, tempString = ConvertOperand(sop, tempString)
        destList, tempString = ConvertOperand(dop, tempString)
        tempString = tempString + destList[0] + " = " + sourceList[0] + ";\n"
        tempString = tempString + destList[1] + " = " + sourceList[1] + ";\n"
        dest64 = GetRegister(dop, 64)
        tempString = tempString + dest64[0] + " = merge(" + destList[1] + ", " + destList[0] + ");\n"
    elif Is64Register(sop) and Is64Register(dop) :
        sourceList, tempString = ConvertOperand(sop, tempString)
        destList, tempString = ConvertOperand(dop, tempString)
        dest64 = GetRegister(dop, 64)[0]
        tempString = tempString + destList[0] + " = " + sourceList[0] + ";\n"
        tempString = tempString + destList[1] + " = " + sourceList[1] + ";\n"
        tempString = tempString + dest64 + " = merge(" + destList[1] + ", " + destList[0] + ");\n"
    else :
        sys.exit("ConvertMovQ: Found a combination of operand I could not recognize\n %s" % (x))

    movqAst = dslparse.dslToAst(tempString)
    return movqAst

def ConvertMovdqa(x) :
    # Mov xmm to 128 bit memory or 128 bit memory to xmm
    tempString = ""
    sourceList = []
    destList = []
    if IsMemory(x[1]) :
        sourceList, tempString = ConvertOperand(x[1], tempString, 32, 128)
    elif Is128Register(x[1]) :
        sourceList, tempString = ConvertOperand(x[1], tempString)
    else :
        sys.exit("ConvertMovqda: unexpected source operand");

    if IsMemory(x[2]) :
        destList, tempString = ConvertOperand(x[2], tempString, 32, 128)
    elif Is128Register(x[2]) :
        destList, tempString = ConvertOperand(x[2], tempString)
    else :
        sys.exit("ConvertMovqda: unexpected source operand");

    for s, d in zip(sourceList, destList) :
        tempString = tempString + d + " = " + s + ";\n"

    movdqaAst = dslparse.dslToAst(tempString)
    return movdqaAst

def ConvertMovdqu(x) :
    # Unaligned mov xmm to 128 bit memory or 128 bit memory to xmm
    tempString = ""
    sourceList = []
    destList = []
    if IsMemory(x[1]) :
        sourceList, tempString = ConvertOperand(x[1], tempString, 32, 128)
    elif Is128Register(x[1]) :
        sourceList, tempString = ConvertOperand(x[1], tempString)
    else :
        sys.exit("ConvertMovqdu: unexpected source operand");

    if IsMemory(x[2]) :
        destList, tempString = ConvertOperand(x[2], tempString, 32, 128)
    elif Is128Register(x[2]) :
        destList, tempString = ConvertOperand(x[2], tempString)
    else :
        sys.exit("ConvertMovqdu: unexpected source operand");

    for s, d in zip(sourceList, destList) :
        tempString = tempString + d + " = " + s + ";\n"

    movdquAst = dslparse.dslToAst(tempString)
    return movdquAst


def ConvertPxor(x) :
    tempString = ""
    sourceList, tempString = ConvertOperand(x[1], tempString)
    destList, tempString = ConvertOperand(x[2], tempString)
    for sl, dl in zip(sourceList, destList) :
        tempString = tempString + dl + " = " + dl + " ^ " + sl + ";\n"

    pxorAst = dslparse.dslToAst(tempString)
    return pxorAst

def ConvertPor(x) :
    tempString = ""
    sourceList, tempString = ConvertOperand(x[1], tempString)
    destList, tempString = ConvertOperand(x[2], tempString)
    for sl, dl in zip(sourceList, destList) :
        tempString = tempString + dl + " = " + dl + " | " + sl + ";\n"

    porAst = dslparse.dslToAst(tempString)
    return porAst

def ConvertPaddd(x) :
    # only vector instructions
    tempString = ""
    sourceList, tempString = ConvertOperand(x[1], tempString)
    destList, tempString = ConvertOperand(x[2], tempString)
    for sl, dl in zip(sourceList, destList) :
        tempString = tempString + dl + " = " + dl + " + " + sl + ";\n"

    padddAst = dslparse.dslToAst(tempString)
    return padddAst

def ConvertPalignr(x) :
    tempString = ""
    shiftByte = int(x[3], 0)
    sourceStr = x[2]
    destStr = x[1]

    # For now, we will only allow shiftByte % 4 == 0
    if shiftByte % 4 != 0 :
        sys.exit("ConvertPalignr only allows shiftByte to be a multiple of 4 for now")

    sourceList, tempString = ConvertOperand(sourceStr, tempString)
    destList, tempString = ConvertOperand(destStr, tempString)

    tempList = ["palignr_temp0", "palignr_temp1", "palignr_temp2", "palignr_temp3"]

    tempString = tempString + tempList[3] + " = " + destList[3] + ";\n" \
                            + tempList[2] + " = " + destList[2] + ";\n" \
                            + tempList[1] + " = " + destList[1] + ";\n" \
                            + tempList[0] + " = " + destList[0] + ";\n"

    tempList2 = ["palignr2_temp0", "palignr2_temp1", "palignr2_temp2", "palignr2_temp3"]

    tempString = tempString + tempList2[3] + " = " + sourceList[3] + ";\n" \
                            + tempList2[2] + " = " + sourceList[2] + ";\n" \
                            + tempList2[1] + " = " + sourceList[1] + ";\n" \
                            + tempList2[0] + " = " + sourceList[0] + ";\n"

    # dest_3 dest_2 dest_1 dest_0 [src_3 src_2 src_1 src_0]    
    if shiftByte == 0 :
        tempString = tempString + destList[3] + " = " + tempList2[3] + ";\n" \
                                + destList[2] + " = " + tempList2[2] + ";\n" \
                                + destList[1] + " = " + tempList2[1] + ";\n" \
                                + destList[0] + " = " + tempList2[0] + ";\n"
        
    # dest_3 dest_2 dest_1 [dest_0 src_3 src_2 src_1] src_0
    elif shiftByte == 4 :
        tempString = tempString + destList[3] + " = " + tempList[0] + ";\n" \
                                + destList[2] + " = " + tempList2[3] + ";\n" \
                                + destList[1] + " = " + tempList2[2] + ";\n" \
                                + destList[0] + " = " + tempList2[1] + ";\n"

    # dest_3 dest_2 [dest_1 dest_0 src_3 src_2] src_1 src_0  
    elif shiftByte == 8 :
        tempString = tempString + destList[3] + " = " + tempList[1] + ";\n" \
                                + destList[2] + " = " + tempList[0] + ";\n" \
                                + destList[1] + " = " + tempList2[3] + ";\n" \
                                + destList[0] + " = " + tempList2[2] + ";\n"

    # dest_3 [dest_2 dest_1 dest_0 src_3] src_2 src_1 src_0
    elif shiftByte == 12 :
        tempString = tempString + destList[3] + " = " + tempList[2] + ";\n" \
                                + destList[2] + " = " + tempList[1] + ";\n" \
                                + destList[1] + " = " + tempList[0] + ";\n" \
                                + destList[0] + " = " + tempList2[3] + ";\n"

    # [dest_3 dest_2 dest_1 dest_0] src_3 src_2 src_1 src_0
    elif shiftByte >= 16 :
        tempString = tempString

    else :
        sys.exit("ConvertPalignr unexpected 1st argument amount: " + shiftByte)
        
    palignrAst = dslparse.dslToAst(tempString)
    
    return palignrAst

def ConvertPsrld(x) :
    tempString = ""
    shiftAmount, tempString = ConvertOperand(x[1], tempString)
    destList, tempString = ConvertOperand(x[2], tempString)

    # dest[3] >> shiftAmount, dest[2] >> shiftAmount, dest[1] >> shiftAmount, dest[0] >> shiftAmount
    tempString = tempString + destList[3] + " = " + destList[3] + " >> " + shiftAmount[0] + ";\n" \
                            + destList[2] + " = " + destList[2] + " >> " + shiftAmount[0] + ";\n" \
                            + destList[1] + " = " + destList[1] + " >> " + shiftAmount[0] + ";\n" \
                            + destList[0] + " = " + destList[0] + " >> " + shiftAmount[0] + ";\n" \

    psrldAst = dslparse.dslToAst(tempString)
    return psrldAst

def ConvertPsrlq(x) :
    tempString = ""
    shiftAmount, tempString = ConvertOperand(x[1], tempString)
    shiftAmount = int(shiftAmount[0], 0)
    destList, tempString = ConvertOperand(x[2], tempString)

    # dest[0..63] >> shiftAmount, dest[64..127] >> shiftAmount
    # destList[0] = concat(split(destList[1], 0, shiftAmount[0] - 1), split(destList[0], 32 - shiftAmount[0], 31) )
    # destList[1] = zeroext(split(destList[1], 32-shiftAmount[0], 31), shiftAmount[0])
    # destList[2] = concat(split(destList[3], 0, shiftAmount[0] - 1), split(destList[2], 32 - shiftAmount[0], 31) )
    # destList[3] = zeroext(split(destList[3], 32-shiftAmount[0], 31), shiftAmount[0])

    tempString = tempString + destList[0] + " = concat(split(" + destList[1] + ", 0, " + str(shiftAmount-1) + "), split(" + destList[0] + ", " + str(shiftAmount) + ", 31));\n" \
                            + destList[1] + " = zeroext(split(" + destList[1] + ", " + str(shiftAmount) + ", 31), " + str(shiftAmount) + ");\n" \
                            + destList[2] + " = concat(split(" + destList[3] + ", 0, " + str(shiftAmount-1) + "), split(" + destList[2] + ", " + str(shiftAmount) + ", 31));\n" \
                            + destList[3] + " = zeroext(split(" + destList[3] + ", " + str(shiftAmount) + ", 31), " + str(shiftAmount) + ");\n"
    

#    tempString = tempString + "psrlq.temp:64 = concat(" + destList[1] + ", " + destList[0] + ");\n" \
#                            + "psrlq.temp:64 = psrlq.temp:64 >> " + shiftAmount[0] + ":64;\n" \
#                            + destList[0] + " = split(psrlq.temp:64, 0, 31);\n" \
#                            + destList[1] + " = split(psrlq.temp:64, 32, 63);\n" \
#                            + "psrlq.temp:64 = concat(" + destList[3] + ", " + destList[2] + ");\n" \
#                            + "psrlq.temp:64 = psrlq.temp:64 >> " + shiftAmount[0] + ":64;\n" \
#                            + destList[2] + " = split(psrlq.temp:64, 0, 31);\n" \
#                            + destList[3] + " = split(psrlq.temp:64, 32, 63);\n"
    psrlqAst = dslparse.dslToAst(tempString)
    return psrlqAst

# Psrldq imm8, xmm1
# if (imm8 > 15) imm8 = 16
# xmm1 = xmm1 >> (imm8 * 8)
def ConvertPsrldq(x) :
    tempString = ""
    destList, tempString = ConvertOperand(x[2], tempString)

    if not isImmediate(x[1]) :
        sys.exit("Psrldq syntax error: " + x[0] + " " + x[1] + " " + x[2])
    shiftAmt = int(x[1], 0)

    # This is a part of the spec for x86
    if shiftAmt > 15 :
        shiftAmt = 16

    # Again, we will only allow imm8 to be multiple of 4.
    if shiftAmt % 4 != 0 :
        sys.exit("Right now, Psrldq only accepts imm8 to be a multiple of 4")

    tempList = ["psrldq_temp0", "psrldq_temp1", "psrldq_temp2", "psrldq_temp3"]

    tempString = tempString + tempList[3] + " = " + destList[3] + ";\n" \
                            + tempList[2] + " = " + destList[2] + ";\n" \
                            + tempList[1] + " = " + destList[1] + ";\n" \
                            + tempList[0] + " = " + destList[0] + ";\n"

    if shiftAmt == 4 :
        tempString = tempString + destList[3] + " = 0;\n" \
                                + destList[2] + " = " + tempList[3] + ";\n" \
                                + destList[1] + " = " + tempList[2] + ";\n" \
                                + destList[0] + " = " + tempList[1] + ";\n"
    if shiftAmt == 8 :
        tempString = tempString + destList[3] + " = 0;\n" \
                                + destList[2] + " = 0;\n" \
                                + destList[1] + " = " + tempList[3] + ";\n" \
                                + destList[0] + " = " + tempList[2] + ";\n"
    if shiftAmt == 12 :
        tempString = tempString + destList[3] + " = 0;\n" \
                                + destList[2] + " = 0;\n" \
                                + destList[1] + " = 0;\n" \
                                + destList[0] + " = " + tempList[3] + ";\n"
    if shiftAmt == 16 :
        tempString = tempString + destList[3] + " = 0;\n" \
                                + destList[2] + " = 0;\n" \
                                + destList[1] + " = 0;\n" \
                                + destList[0] + " = 0;\n"

    psrldqAst = dslparse.dslToAst(tempString)
    return psrldqAst

# Pslldq imm8, xmm1
# if (imm8 > 15) imm8 = 16
# xmm1 = xmm1 << (imm8 * 8)
def ConvertPslldq(x) :
    tempString = ""
    destList, tempString = ConvertOperand(x[2], tempString)

    if not isImmediate(x[1]) :
        sys.exit("Pslldq syntax error: " + x[0] + " " + x[1] + " " + x[2])
    shiftAmt = int(x[1], 0)

    # This is a part of the spec for x86
    if shiftAmt > 15 :
        shiftAmt = 16

    # Again, we will only allow imm8 to be multiple of 4.
    if shiftAmt % 4 != 0 :
        sys.exit("Right now, Pslldq only accepts imm8 to be a multiple of 4")
        exit(1)

    tempList = ["pslldq_temp0", "pslldq_temp1", "pslldq_temp2", "pslldq_temp3"]

    tempString = tempString + tempList[3] + " = " + destList[3] + ";\n" \
                            + tempList[2] + " = " + destList[2] + ";\n" \
                            + tempList[1] + " = " + destList[1] + ";\n" \
                            + tempList[0] + " = " + destList[0] + ";\n"

    if shiftAmt == 4 :
        tempString = tempString + destList[3] + " = " + tempList[2] + ";\n" \
                                + destList[2] + " = " + tempList[1] + ";\n" \
                                + destList[1] + " = " + tempList[0] + ";\n" \
                                + destList[0] + " = 0;\n"
    if shiftAmt == 8 :
        tempString = tempString + destList[3] + " = " + tempList[1] + ";\n" \
                                + destList[2] + " = " + tempList[0] + ";\n" \
                                + destList[1] + " = 0;\n" \
                                + destList[0] + " = 0;\n"
    if shiftAmt == 12 :
        tempString = tempString + destList[3] + " = " + tempList[0] + ";\n" \
                                + destList[2] + " = 0;\n" \
                                + destList[1] + " = 0;\n" \
                                + destList[0] + " = 0;\n"
    if shiftAmt == 16 :
        tempString = tempString + destList[3] + " = 0;\n" \
                                + destList[2] + " = 0;\n" \
                                + destList[1] + " = 0;\n" \
                                + destList[0] + " = 0;\n"

    psrldqAst = dslparse.dslToAst(tempString)
    return psrldqAst

def ConvertPslld(x) :
    tempString = ""
    shiftAmount, tempString = ConvertOperand(x[1], tempString)
    destList, tempString = ConvertOperand(x[2], tempString)

    # dest[3] >> shiftAmount, dest[2] >> shiftAmount, dest[1] >> shiftAmount, dest[0] >> shiftAmount
    tempString = tempString + destList[3] + " = " + destList[3] + " << " + shiftAmount[0] + ";\n" \
                            + destList[2] + " = " + destList[2] + " << " + shiftAmount[0] + ";\n" \
                            + destList[1] + " = " + destList[1] + " << " + shiftAmount[0] + ";\n" \
                            + destList[0] + " = " + destList[0] + " << " + shiftAmount[0] + ";\n" \

    psrldAst = dslparse.dslToAst(tempString)
    return psrldAst

# pshufd imm8, xmm2/m128, xmm1
# Shuffle the doublewords in xmm2/m128 based on the encoding in imm8 and store the result in xmm1.
#DEST[31:0] (SRC >> (ORDER[1:0] * 32))[31:0];
#DEST[63:32] (SRC >> (ORDER[3:2] * 32))[31:0];
#DEST[95:64] (SRC >> (ORDER[5:4] * 32))[31:0];
#DEST[127:96] (SRC >> (ORDER[7:6] * 32))[31:0];
def ConvertPshufd(x) :
    tempString = ""
    if not isImmediate(x[1]) :
        sys.exit("We only support AT&T GAS syntax: Pshufd imm8, xmm2/m128, xmm1. ")

    shufAmount = int(x[1], 0)
    sourceList, tempString = ConvertOperand(x[2], tempString)
    destList, tempString = ConvertOperand(x[3], tempString)

    tempList = ["pslldq_temp0", "pslldq_temp1", "pslldq_temp2", "pslldq_temp3"]

    tempString = tempString + tempList[3] + " = " + sourceList[3] + ";\n" \
                            + tempList[2] + " = " + sourceList[2] + ";\n" \
                            + tempList[1] + " = " + sourceList[1] + ";\n" \
                            + tempList[0] + " = " + sourceList[0] + ";\n"

    for i in range(0, 4) :
        srcIndex = (shufAmount >> (i * 2)) & 3
        tempString = tempString + destList[i] + " = " + tempList[srcIndex] + ";\n"

    pshufdAst = dslparse.dslToAst(tempString)
    return pshufdAst

def ConvertPshufb(x) :
    assert(len(x) == 3)
    # Based on the value of x[1], swap bytes in x[2]
    sourceList, tempString = ConvertOperand(x[1], "")
    destList, tempString = ConvertOperand(x[2], tempString)

    for i in range(0, 4) :
        tempString = tempString + "temp:8 = split(" + sourceList[0] + ", " + str(i * 8) + ", " + str(i * 8 + 7) + ");\n"
        tempString = tempString + "dest_temp" + str(i) + "_case0:8 = 0:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case1:8 = temp:8 == 0:8 ? split(" + destList[0] + ", 0, 7) : dest_temp" + str(i) + "_case0:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case2:8 = temp:8 == 1:8 ? split(" + destList[0] + ", 8, 15) : dest_temp" + str(i) + "_case1:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case3:8 = temp:8 == 2:8 ? split(" + destList[0] + ", 16, 23) : dest_temp" + str(i) + "_case2:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case4:8 = temp:8 == 3:8 ? split(" + destList[0] + ", 24, 31) : dest_temp" + str(i) + "_case3:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case5:8 = temp:8 == 4:8 ? split(" + destList[1] + ", 0, 7) : dest_temp" + str(i) + "_case4:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case6:8 = temp:8 == 5:8 ? split(" + destList[1] + ", 8, 15) : dest_temp" + str(i) + "_case5:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case7:8 = temp:8 == 6:8 ? split(" + destList[1] + ", 16, 23) : dest_temp" + str(i) + "_case6:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case8:8 = temp:8 == 7:8 ? split(" + destList[1] + ", 24, 31) : dest_temp" + str(i) + "_case7:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case9:8 = temp:8 == 8:8 ? split(" + destList[2] + ", 0, 7) : dest_temp" + str(i) + "_case8:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case10:8 = temp:8 == 9:8 ? split(" + destList[2] + ", 8, 15) : dest_temp" + str(i) + "_case9:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case11:8 = temp:8 == 10:8 ? split(" + destList[2] + ", 16, 23) : dest_temp" + str(i) + "_case10:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case12:8 = temp:8 == 11:8 ? split(" + destList[2] + ", 24, 31) : dest_temp" + str(i) + "_case11:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case13:8 = temp:8 == 12:8 ? split(" + destList[3] + ", 0, 7) : dest_temp" + str(i) + "_case12:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case14:8 = temp:8 == 13:8 ? split(" + destList[3] + ", 8, 15) : dest_temp" + str(i) + "_case13:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case15:8 = temp:8 == 14:8 ? split(" + destList[3] + ", 16, 23) : dest_temp" + str(i) + "_case14:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case16:8 = temp:8 == 15:8 ? split(" + destList[3] + ", 24, 31) : dest_temp" + str(i) + "_case15:8;\n"

    for i in range(4, 8) :
        tempString = tempString + "temp:8 = split(" + sourceList[1] + ", " + str((i-4) * 8) + ", " + str((i-4) * 8 + 7) + ");\n"
        tempString = tempString + "dest_temp" + str(i) + "_case0:8 = 0:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case1:8 = temp:8 == 0:8 ? split(" + destList[0] + ", 0, 7) : dest_temp" + str(i) + "_case0:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case2:8 = temp:8 == 1:8 ? split(" + destList[0] + ", 8, 15) : dest_temp" + str(i) + "_case1:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case3:8 = temp:8 == 2:8 ? split(" + destList[0] + ", 16, 23) : dest_temp" + str(i) + "_case2:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case4:8 = temp:8 == 3:8 ? split(" + destList[0] + ", 24, 31) : dest_temp" + str(i) + "_case3:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case5:8 = temp:8 == 4:8 ? split(" + destList[1] + ", 0, 7) : dest_temp" + str(i) + "_case4:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case6:8 = temp:8 == 5:8 ? split(" + destList[1] + ", 8, 15) : dest_temp" + str(i) + "_case5:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case7:8 = temp:8 == 6:8 ? split(" + destList[1] + ", 16, 23) : dest_temp" + str(i) + "_case6:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case8:8 = temp:8 == 7:8 ? split(" + destList[1] + ", 24, 31) : dest_temp" + str(i) + "_case7:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case9:8 = temp:8 == 8:8 ? split(" + destList[2] + ", 0, 7) : dest_temp" + str(i) + "_case8:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case10:8 = temp:8 == 9:8 ? split(" + destList[2] + ", 8, 15) : dest_temp" + str(i) + "_case9:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case11:8 = temp:8 == 10:8 ? split(" + destList[2] + ", 16, 23) : dest_temp" + str(i) + "_case10:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case12:8 = temp:8 == 11:8 ? split(" + destList[2] + ", 24, 31) : dest_temp" + str(i) + "_case11:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case13:8 = temp:8 == 12:8 ? split(" + destList[3] + ", 0, 7) : dest_temp" + str(i) + "_case12:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case14:8 = temp:8 == 13:8 ? split(" + destList[3] + ", 8, 15) : dest_temp" + str(i) + "_case13:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case15:8 = temp:8 == 14:8 ? split(" + destList[3] + ", 16, 23) : dest_temp" + str(i) + "_case14:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case16:8 = temp:8 == 15:8 ? split(" + destList[3] + ", 24, 31) : dest_temp" + str(i) + "_case15:8;\n"

    for i in range(8, 12) :
        tempString = tempString + "temp:8 = split(" + sourceList[2] + ", " + str((i-8) * 8) + ", " + str((i-8) * 8 + 7) + ");\n"
        tempString = tempString + "dest_temp" + str(i) + "_case0:8 = 0:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case1:8 = temp:8 == 0:8 ? split(" + destList[0] + ", 0, 7) : dest_temp" + str(i) + "_case0:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case2:8 = temp:8 == 1:8 ? split(" + destList[0] + ", 8, 15) : dest_temp" + str(i) + "_case1:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case3:8 = temp:8 == 2:8 ? split(" + destList[0] + ", 16, 23) : dest_temp" + str(i) + "_case2:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case4:8 = temp:8 == 3:8 ? split(" + destList[0] + ", 24, 31) : dest_temp" + str(i) + "_case3:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case5:8 = temp:8 == 4:8 ? split(" + destList[1] + ", 0, 7) : dest_temp" + str(i) + "_case4:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case6:8 = temp:8 == 5:8 ? split(" + destList[1] + ", 8, 15) : dest_temp" + str(i) + "_case5:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case7:8 = temp:8 == 6:8 ? split(" + destList[1] + ", 16, 23) : dest_temp" + str(i) + "_case6:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case8:8 = temp:8 == 7:8 ? split(" + destList[1] + ", 24, 31) : dest_temp" + str(i) + "_case7:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case9:8 = temp:8 == 8:8 ? split(" + destList[2] + ", 0, 7) : dest_temp" + str(i) + "_case8:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case10:8 = temp:8 == 9:8 ? split(" + destList[2] + ", 8, 15) : dest_temp" + str(i) + "_case9:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case11:8 = temp:8 == 10:8 ? split(" + destList[2] + ", 16, 23) : dest_temp" + str(i) + "_case10:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case12:8 = temp:8 == 11:8 ? split(" + destList[2] + ", 24, 31) : dest_temp" + str(i) + "_case11:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case13:8 = temp:8 == 12:8 ? split(" + destList[3] + ", 0, 7) : dest_temp" + str(i) + "_case12:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case14:8 = temp:8 == 13:8 ? split(" + destList[3] + ", 8, 15) : dest_temp" + str(i) + "_case13:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case15:8 = temp:8 == 14:8 ? split(" + destList[3] + ", 16, 23) : dest_temp" + str(i) + "_case14:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case16:8 = temp:8 == 15:8 ? split(" + destList[3] + ", 24, 31) : dest_temp" + str(i) + "_case15:8;\n"

    for i in range(12, 16) :
        tempString = tempString + "temp:8 = split(" + sourceList[3] + ", " + str((i-12) * 8) + ", " + str((i-12) * 8 + 7) + ");\n"
        tempString = tempString + "dest_temp" + str(i) + "_case0:8 = 0:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case1:8 = temp:8 == 0:8 ? split(" + destList[0] + ", 0, 7) : dest_temp" + str(i) + "_case0:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case2:8 = temp:8 == 1:8 ? split(" + destList[0] + ", 8, 15) : dest_temp" + str(i) + "_case1:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case3:8 = temp:8 == 2:8 ? split(" + destList[0] + ", 16, 23) : dest_temp" + str(i) + "_case2:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case4:8 = temp:8 == 3:8 ? split(" + destList[0] + ", 24, 31) : dest_temp" + str(i) + "_case3:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case5:8 = temp:8 == 4:8 ? split(" + destList[1] + ", 0, 7) : dest_temp" + str(i) + "_case4:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case6:8 = temp:8 == 5:8 ? split(" + destList[1] + ", 8, 15) : dest_temp" + str(i) + "_case5:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case7:8 = temp:8 == 6:8 ? split(" + destList[1] + ", 16, 23) : dest_temp" + str(i) + "_case6:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case8:8 = temp:8 == 7:8 ? split(" + destList[1] + ", 24, 31) : dest_temp" + str(i) + "_case7:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case9:8 = temp:8 == 8:8 ? split(" + destList[2] + ", 0, 7) : dest_temp" + str(i) + "_case8:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case10:8 = temp:8 == 9:8 ? split(" + destList[2] + ", 8, 15) : dest_temp" + str(i) + "_case9:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case11:8 = temp:8 == 10:8 ? split(" + destList[2] + ", 16, 23) : dest_temp" + str(i) + "_case10:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case12:8 = temp:8 == 11:8 ? split(" + destList[2] + ", 24, 31) : dest_temp" + str(i) + "_case11:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case13:8 = temp:8 == 12:8 ? split(" + destList[3] + ", 0, 7) : dest_temp" + str(i) + "_case12:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case14:8 = temp:8 == 13:8 ? split(" + destList[3] + ", 8, 15) : dest_temp" + str(i) + "_case13:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case15:8 = temp:8 == 14:8 ? split(" + destList[3] + ", 16, 23) : dest_temp" + str(i) + "_case14:8;\n"
        tempString = tempString + "dest_temp" + str(i) + "_case16:8 = temp:8 == 15:8 ? split(" + destList[3] + ", 24, 31) : dest_temp" + str(i) + "_case15:8;\n"

    tempString = tempString + destList[0] + " = merge(dest_temp3_case16:8, merge(dest_temp2_case16:8, merge(dest_temp1_case16:8, dest_temp0_case16:8)));\n"
    tempString = tempString + destList[1] + " = merge(dest_temp7_case16:8, merge(dest_temp6_case16:8, merge(dest_temp5_case16:8, dest_temp4_case16:8)));\n"
    tempString = tempString + destList[2] + " = merge(dest_temp11_case16:8, merge(dest_temp10_case16:8, merge(dest_temp9_case16:8, dest_temp8_case16:8)));\n"
    tempString = tempString + destList[3] + " = merge(dest_temp15_case16:8, merge(dest_temp14_case16:8, merge(dest_temp13_case16:8, dest_temp12_case16:8)));\n"
    
    pshufbAst = dslparse.dslToAst(tempString)
    return pshufbAst
    

def ConvertJnz(x) :
    destList, tempString = ConvertOperand(x[1])
    dest = destList[0]
    tempString = tempString + "jmp zf:1 == 0:1 ? " + dest + " : L$NONE;"

    jnzAst = dslparse.dslToAst(tempString)
    return jnzAst

def ConvertJz(x) :
    destList, tempString = ConvertOperand(x[1])
    dest = destList[0]
    tempString = "jmp zf:1 == 1:1 ? " + dest + " : L$NONE;"

    jzAst= dslparse.dslToAst(tempString)
    return jzAst

def ConvertJmp(x) :
    destList, tempString = ConvertOperand(x[1])
    dest = destList[0]
    tempString = "jmp 1:1 == 1:1 ? " + dest + " : L$NONE;"

    jmpAst = dslparse.dslToAst(tempString)
    return jmpAst

def ConvertDefault(x) :
    sys.exit("Please implement Convert for:\n %s" % (x))

def ConvertToDsl(x86Insts) :
    retList = []
    for x86I in x86Insts :
        convFunc = convertSwitcher.get(x86I[0], ConvertDefault)
        insts = convFunc(x86I)
        retList.extend(insts)
    return retList

convertSwitcher = {
    "movl" : ConvertMovl,
    "movd" : ConvertMovd,
    "movq" : ConvertMovq,
    "movdqa" : ConvertMovdqa,
    "addl" : ConvertAddl,
    "adcl" : ConvertAdcl,
    "cmpl" : ConvertCmpl,
    "cmpq" : ConvertCmpq,
    "decl" : ConvertDecl,
    "xorl" : ConvertXorl,
    "andl" : ConvertAndl,
    "shrl" : ConvertShrl,
    "shrq" : ConvertShrq,
    "shlq" : ConvertShlq,
    "rorl" : ConvertRorl,
    "roll" : ConvertRoll,
    "jnz" : ConvertJnz,
    "jz" : ConvertJz,
    "jmp" : ConvertJmp,
    "paddd" : ConvertPaddd,
    "subq" : ConvertSubq,
    "movdqu" : ConvertMovdqu,
    "por" : ConvertPor,
    "pxor" : ConvertPxor,
    "leaq" : ConvertLeaq,
    "subl" : ConvertSubl,
    "movzbl" : ConvertMovzbl,
    "palignr" : ConvertPalignr,
    "psrld" : ConvertPsrld,
    "pslld" : ConvertPslld,
    "andq" : ConvertAndq,
    "addq" : ConvertAddq,
    "psrlq" : ConvertPsrlq,
    "pshufd" : ConvertPshufd,
    "psrldq" : ConvertPsrldq,
    "pslldq" : ConvertPslldq,
    "bswapl" : ConvertBswapl,
    "cmpb" : ConvertCmpb,
    "pshufb" : ConvertPshufb,
    "cmovzl" : ConvertCmovzl,
    "cmovnzl" : ConvertCmovnzl,
    "cmovel" : ConvertCmovel,
    "cmovnel" : ConvertCmovnel,
    "cmovgel" : ConvertCmovgel,
    "cmovll" : ConvertCmovll,
    "cmovlel" : ConvertCmovlel,
    "cmovgl" : ConvertCmovgl,
    "cmovncl" : ConvertCmovncl,
    "cmovol" : ConvertCmovol,
    "cmovnol" : ConvertCmovnol
}
