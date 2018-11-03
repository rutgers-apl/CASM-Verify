import pyparse.pyparsing as pp
import config
import sys

#########################################################################################################
# Contains helper methods and sturctures for x86todsl                                                   #
# Think of it like the .h file of x86todsl. Any helper method should be here                            #
#########################################################################################################

# Low 8bit register dictionary
reg8low = {0 : "al", \
           1 : "bl", \
           2 : "cl", \
           3 : "dl"}
reg8lowRev = {v: k for k, v in reg8low.items()}

# High 8bit register dictionary
reg8high = {0 : "ah", \
            1 : "bh", \
            2 : "ch", \
            3 : "dh"}
reg8highRev = {v: k for k, v in reg8high.items()}

# 32bit register dictionary
reg32 = {0 : "eax", \
         1 : "ebx", \
         2 : "ecx", \
         3 : "edx", \
         4 : "esp", \
         5 : "ebp", \
         6 : "esi", \
         7 : "edi", \
         8 : "r8d", \
         9 : "r9d", \
         10: "r10d",\
         11: "r11d",\
         12: "r12d",\
         13: "r13d",\
         14: "r14d",\
         15: "r15d",\
         16: "eip"}
reg32Rev= {v: k for k, v in reg32.items()}

# 64bit register dictionary
reg64 = {0 : "rax", \
         1 : "rbx", \
         2 : "rcx", \
         3 : "rdx", \
         4 : "rsp", \
         5 : "rbp", \
         6 : "rsi", \
         7 : "rdi", \
         8 : "r8", \
         9 : "r9", \
         10: "r10", \
         11: "r11", \
         12: "r12", \
         13: "r13", \
         14: "r14", \
         15: "r15",\
         16: "rip"}
reg64Rev= {v: k for k, v in reg64.items()}

# 128bit vector register dictionary
reg128 = {0 : "xmm0", \
          1 : "xmm1", \
          2 : "xmm2", \
          3 : "xmm3", \
          4 : "xmm4", \
          5 : "xmm5", \
          6 : "xmm6", \
          7 : "xmm7"}
reg128Rev= {v: k for k, v in reg128.items()}

##################################################################################
#                                  Helper methods.                               #
##################################################################################

# Is val a number?
def isImmediate(val) :
    try:
        val = int(val, 0)
        return True
    except :
        return False

def Get32BitRepFromRegister(o) :
    if isinstance(o, str) and o in reg32Rev :
        return [o]
    elif isinstance(o, str) and o in reg64Rev :
        index = reg64Rev[o]
        return [reg32[index], o + "_1"]
    elif isinstance(o, str) and o in reg128Rev :
        return [o + "_0", o + "_1", o + "_2", o + "_3"]
    else : sys.exit("Get32BitRepFromRegister: " + o + "is not a register I can recognize")

def Get64BitRepFromRegister(o) :
    assert(config.Is64BitArch())
    if isinstance(o, str) and o in reg32Rev :
        index = reg32Rev[o]
        return [reg64[index] + ":64"]
    elif isinstance(o, str) and o in reg64Rev :
        return [o + ":64"]
    elif isinstance(o, str) and o in reg128Rev :
        return [o + "_64_0:64", o + "_64_0:64"]
    else : sys.exit("Get64BitRepFromRegister: " + o + "is not a register I can recognize")

def Get128BitRepFromRegister(o) :
    if isinstance(o, str) and o in reg128Rev :
        return [o + ":128"]
    else : sys.exit("Get128BitRepFromRegister: Cannot represent " + o + "as a 128bit.")

# Gets the correct representation of the register. Adds "bitsize" syntax as well.
def GetRegister(o, bitlength = 32) :
    if bitlength == 32:
        return Get32BitRepFromRegister(o)
    elif bitlength == 64:
        return Get64BitRepFromRegister(o)
    else:
        return Get128BitRepFromRegister(o)

def Is8Register(o) :
    if isinstance(o, str) and o in reg8lowRev :
        return True
    elif isinstance(o, str) and o in reg8highRev :
        return True
    return False
    
def Is32Register(o) :
    if isinstance(o, str) and o in reg32Rev :
        return True
    return False

def Is64Register(o) :
    if isinstance(o, str) and o in reg64Rev :
        return True
    return False

def Is128Register(o) :
    if isinstance(o, str) and o in reg128Rev :
        return True
    return False

def IsMemory(o) :
    if isinstance(o, pp.ParseResults) or isinstance(o, list) :
        return True
    return False

def IsRegister(o) :
    return Is32Register(o) or Is64Register(o) or Is128Register(o)

def CalculateAddress(o) :
    # ['OFFSET', 'rax']
    # ['OFFSET', 'rax', 'rdx']
    # ['OFFSET', 'rax', 'rdx', '8']
    # ['OFFSET', 'BASE', 'rdx', '8']

    assert(len(o) > 1)
    regSize = ":64"
    if config.Is32BitArch() : regSize = ":32"
    # We will always get ['OFFSET', 'BASE']
    addrString = ""
    if o[1] != 'BASE' :
        # Then we have base register
        baseReg = ""
        if config.Is64BitArch() :
            baseReg = Get64BitRepFromRegister(o[1])[0]
        elif config.Is32BitArch() :
            baseReg = Get32BitRepFromRegister(o[1])[0]
        if baseReg != "" : addrString = addrString + baseReg

    shiftValue = 0
    if (len(o) == 4) :
        # Addressing mode specifies shiftValue. By definition, o[3] can only be 1, 2, 4, or 8
        if o[3] == '1' : shiftValue = 0
        elif o[3] == '2' : shiftValue = 1
        elif o[3] == '4' : shiftValue = 2
        elif o[3] == '8' : shiftValue = 3
        else : sys.exit("Illegal index multiplier value: %s" + (o))

    if (len(o) >= 3) :
        # Then we have to add additional register
        if config.Is64BitArch() :
            indexReg = Get64BitRepFromRegister(o[2])[0]
        elif config.Is32BitArch() :
            indexReg = Get32BitRepFromRegister(o[2])[0]

        if addrString != "" : addrString = addrString + " + "
        if shiftValue == 0 : addrString = addrString + indexReg
        else : addrString = addrString + "(" + indexReg + " << " + str(shiftValue) + regSize + ")"

    if o[0] != 'OFFSET' and o[0] != '0': addrString = addrString + " + " + o[0] + regSize

    return addrString
    
def ConvertOperand(o, tempString = "", bitlength = 32, forceSize = 32) :
    # This is memory addressing mode.
    if isinstance(o, pp.ParseResults) or isinstance(o, list) :
        retList = []
        # Identify the bitlength of the register used for memory access.
        regSize = ":64"
        if config.Is32BitArch() :
            regSize = ":32"

        # Add base register
        taddr = o[1] + regSize

        # Add index and scale
        if len(o) == 4 :
            index = o[2] + regSize
            multiplier = int(o[3])
            if multiplier == 1 : taddr = taddr + " + " + index
            elif multiplier == 2 : taddr = taddr + " + (" + index + " << 1" + regSize + ") "
            elif multiplier == 4 : taddr = taddr + " + (" + index + " << 2" + regSize + ") "
            elif multiplier == 8 : taddr = taddr + " + (" + index + " << 3" + regSize + ") "
            else : taddr = taddr + " + " + index

        offset = 0 if o[0] == "OFFSET" else int(o[0])
        if offset % 4 == 0 :
            # Then we have no problem.
            if offset != 0 :
                taddr = taddr + " + " + str(offset) + regSize
            forceSizeAdd = 0
            while forceSizeAdd < 128 :
                # for example if bitlength = 32, forceSize = 128
                # we should get +0, +4, +8, and +12
                finalAddr = taddr + " + " + str(int(forceSizeAdd / 8)) + regSize
                retList.append("mem[" + finalAddr + "]")
                forceSizeAdd = forceSizeAdd + bitlength
            return retList, tempString
        else :
            # We gotta start thinking about offset memory loads.
            newoffset = int(offset / 4)
            offsetrem = offset % 4
            taddrlow = taddr if newoffset == 0 else (taddr + " + " + str(newoffset) + regSize)
            taddrhigh = (taddr + " + 4" + regSize + " ") if newoffset == 0 else (taddr + " + " + str(newoffset + 4) + regSize)
            while forceSize > 0 :
                forceoffset = int((forceSize - bitlength) / 8)
                if not forceoffset == 0 :
                    taddrlow = taddrlow + " + " + str(forceoffset) + regSize
                    taddrhigh = taddrhigh + " + " + str(forceoffset) + regSize
                # example: 3(%r14) -> merge(split(mem[r14 + 4], 0, 23), split(mem[r14], 24, 31))
                tempString = tempString + "cavtmemhigh" + str(forceoffset) + ":" + str(offsetrem * 8) + \
                             " = split(mem[" + taddrhigh + "], 0, " + str(offsetrem * 8 - 1) + ");\n"
                             
                tempString = tempString + "cavtmemlow" + str(forceoffset) + ":" + str((4-offsetrem) * 8) + \
                             " = split(mem[" + taddrlow + "], " + str(offsetrem * 8) + ", 31);\n"
                             
                tempString = tempString + "cavtmem" + str(forceoffset) + " = merge(cavtmemhigh" + \
                             str(forceoffset) + ":" + str(offsetrem * 8) + ", cavtmemlow" + \
                             str(forceoffset) + ":" + str((4-offset) * 8) + ");\n"
                             
                retList.append("cavtmem" + str(forceoffset))
                forceSize = forceSize - bitlength
            return retList, tempString
    elif o.startswith("L$") :
        return [o], tempString
    elif isImmediate(o) :
        if bitlength > 32 :
            return [o + ":" + str(bitlength)], tempString
        return [o], tempString
    elif o in reg32Rev :
        return GetRegister(o, bitlength), tempString
    elif o in reg64Rev :
        return GetRegister(o, bitlength), tempString
    elif o in reg128Rev :
        rName = o
        return [rName + "_0", rName + "_1", rName + "_2", rName + "_3"], tempString
    else : sys.exit("I don't know what", o, "is in x86 operand.")
