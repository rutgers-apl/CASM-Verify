bold=$(tput bold)
normal=$(tput sgr0)

echo "${bold}Testing Hard to Detect Bugs.${normal}"
echo "${bold}42 benchmarks total.${normal}"
echo "${bold}Total Expected Required Time: ~ 18 hours 15 minutes.${normal}"
echo ""

echo "${bold}Hard to Detect Bug #1${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
echo "${bold}Expected Required Time: ~2 minutes${normal}"
python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm1 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #2${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~2 hour 10 minutes${normal}"
python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm3 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #3${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~22 minutes${normal}"
python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm4 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #4${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~30 minutes${normal}"
python3 main.py --pre test/sha256/diffInst/pre5 --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm5 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #5${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~29 minutes${normal}"
python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm6 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #6${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~23 minutes${normal}"
python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm7 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #7${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~22 minutes${normal}"
python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm8 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #8${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~34 minutes${normal}"
python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm9 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #9${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~60 minutes${normal}"
python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm1 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #10${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~47 minutes${normal}"
python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm3 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #11${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
echo "${bold}Expected Required Time: ~2 minutes${normal}"
python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm8 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #12${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~31 minutes${normal}"
python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm9 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #13${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~52 minutes${normal}"
python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm10 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #14${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
echo "${bold}Expected Required Time: ~2 minutes${normal}"
python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm11 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #15${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~30 minutes${normal}"
python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm12 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #16${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~52 minutes${normal}"
python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm13 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #17${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~45 minutes${normal}"
python3 main.py --pre test/sha256_ssse3/pre --post test/sha256_ssse3/post --p1 test/sha256_ssse3/dsl --p1lang dsl --p2 test/sha256_ssse3/diffInst/asm14 --p2lang asm --arch x86_64
echo ""

echo "${bold}Hard to Detect Bug #18${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~60 minutes${normal}"
python3 main.py --pre test/AES_encrypt/pre --post test/AES_encrypt/post --p1 test/AES_encrypt/dsl --p1lang dsl --p2 test/AES_encrypt/diffInst/asm1 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #19${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2(Reason: Output semantically different)${normal}"
echo "${bold}Expected Required Time: ~17 minutes${normal}"
python3 main.py --pre test/AES_encrypt/pre --post test/AES_encrypt/post --p1 test/AES_encrypt/dsl --p1lang dsl --p2 test/AES_encrypt/diffInst/asm2 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #20${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2(Reason: Output semantically different)${normal}"
echo "${bold}Expected Required Time: ~17 minutes${normal}"
python3 main.py --pre test/AES_encrypt/pre --post test/AES_encrypt/post --p1 test/AES_encrypt/dsl --p1lang dsl --p2 test/AES_encrypt/diffInst/asm3 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #21${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~44 minutes${normal}"
python3 main.py --pre test/AES_encrypt/pre --post test/AES_encrypt/post --p1 test/AES_encrypt/dsl --p1lang dsl --p2 test/AES_encrypt/diffInst/asm5 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #22${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2(Reason: Output semantically different)"
echo "${bold}Expected Required Time: ~1 hour 25 minutes${normal}"
python3 main.py --pre test/AES_encrypt_key_expansion/pre --post test/AES_encrypt_key_expansion/post --p1 test/AES_encrypt_key_expansion/dsl --p1lang dsl --p2 test/AES_encrypt_key_expansion/diffInst/asm2 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #23${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
echo "${bold}Expected Required Time: < 1 seconds${normal}"
python3 main.py --pre test/AES_encrypt_key_expansion/pre --post test/AES_encrypt_key_expansion/post --p1 test/AES_encrypt_key_expansion/dsl --p1lang dsl --p2 test/AES_encrypt_key_expansion/diffInst/asm3 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #24${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
echo "${bold}Expected Required Time: ~1 minute${normal}"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm1 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #25${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2(Reason: Output semantically different)${normal}"
echo "${bold}Expected Required Time: ~22 minute${normal}"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm3 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #26${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2(Reason: Output semantically different)${normal}"
echo "${bold}Expected Required Time: ~24 minute${normal}"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm4 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #27${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2(Reason: Output semantically different)${normal}"
echo "${bold}Expected Required Time: ~23 minute${normal}"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm5 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #28${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2(Reason: Output semantically different)${normal}"
echo "${bold}Expected Required Time: ~23 minute${normal}"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm6 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #29${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2(Reason: Output semantically different)${normal}"
echo "${bold}Expected Required Time: ~23 minute${normal}"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm10 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #30${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2(Reason: Output semantically different)${normal}"
echo "${bold}Expected Required Time: ~23 minute${normal}"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm11 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #31${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2(Reason: Output semantically different)${normal}"
echo "${bold}Expected Required Time: ~23 minute${normal}"
python3 main.py --pre test/AES_dec_key_permute/pre --post test/AES_dec_key_permute/post --p1 test/AES_dec_key_permute/dsl --p1lang dsl --p2 test/AES_dec_key_permute/diffInst/asm12 --p2lang asm --arch x86_64 --mem_model 8
echo ""

echo "${bold}Hard to Detect Bug #32${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~35 minute${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm1 --p2lang asm
echo ""

echo "${bold}Hard to Detect Bug #33${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
echo "${bold}Expected Required Time: < 1 minute${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm2 --p2lang asm
echo ""

echo "${bold}Hard to Detect Bug #34${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
echo "${bold}Expected Required Time: < 1 minute${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm3 --p2lang asm
echo ""

echo "${bold}Hard to Detect Bug #35${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
echo "${bold}Expected Required Time: < 1 minute${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm4 --p2lang asm
echo ""

echo "${bold}Hard to Detect Bug #36${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
echo "${bold}Expected Required Time: < 1 minute${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm5 --p2lang asm
echo ""

echo "${bold}Hard to Detect Bug #37${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: < 1 minute${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm6 --p2lang asm
echo ""

echo "${bold}Hard to Detect Bug #38${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
echo "${bold}Expected Required Time: < 1 minute${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm7 --p2lang asm
echo ""

echo "${bold}Hard to Detect Bug #39${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
echo "${bold}Expected Required Time: < 1 minute${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm8 --p2lang asm
echo ""

echo "${bold}Hard to Detect Bug #40${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~7 minute${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm9 --p2lang asm
echo ""

echo "${bold}Hard to Detect Bug #41${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~7 minute${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm10 --p2lang asm
echo ""

echo "${bold}Hard to Detect Bug #42${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: SMT Timeout)${normal}"
echo "${bold}Expected Required Time: ~32 minute${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/cmov/asm11 --p2lang asm
echo ""
