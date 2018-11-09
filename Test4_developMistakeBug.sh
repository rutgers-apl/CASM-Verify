bold=$(tput bold)
normal=$(tput sgr0)

echo "${bold}Testing Buggy Implementation due to Developer Mitake.${normal}"
echo "${bold}40 benchmarks total.${normal}"
echo "${bold}Total Expected Required Time: ~25 minutes.${normal}"
echo ""

echo "${bold}Developer Mistake #1${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/swappedOperand/asm1 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #2${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/swappedOperand/asm2 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #3${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/swappedOperand/asm3 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #4${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/swappedOperand/asm4 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #5${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/swappedOperand/asm5 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #6${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/swappedOperand/asm6 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #7${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/swappedOperand/asm7 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #8${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/swappedOperand/asm8 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #9${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/swappedOperand/asm9 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #10${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/swappedOperand/asm10 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #11${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongAddr/asm1 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #12${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongAddr/asm2 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #13${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongAddr/asm3 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #14${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongAddr/asm4 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #15${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongAddr/asm5 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #16${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongAddr/asm6 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #17${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongAddr/asm7 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #18${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongAddr/asm8 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #19${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongAddr/asm9 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #20${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongAddr/asm10 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #21${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongInst/asm1 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #22${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongInst/asm2 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #23${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongInst/asm3 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #24${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongInst/asm4 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #25${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongInst/asm5 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #26${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongInst/asm6 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #27${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongInst/asm7 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #28${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongInst/asm8 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #29${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongInst/asm9 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #30${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongInst/asm10 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #31${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongOperand/asm1 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #32${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongOperand/asm2 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #33${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongOperand/asm3 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #34${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongOperand/asm4 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #35${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongOperand/asm5 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #36${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongOperand/asm6 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #37${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongOperand/asm7 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #38${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongOperand/asm8 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #39${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongOperand/asm9 --p2lang asm --verif_mode hybrid
echo ""

echo "${bold}Developer Mistake #40${normal}"
echo "${bold}Expected result: p1 is not equivalent to p2 (Reason: Concrete Execution)${normal}"
python3 main.py --pre test/ChaCha20/pre --post test/ChaCha20/post --p1 test/ChaCha20/dsl --p1lang dsl --p2 test/ChaCha20/wrongOperand/asm10 --p2lang asm --verif_mode hybrid
echo ""
