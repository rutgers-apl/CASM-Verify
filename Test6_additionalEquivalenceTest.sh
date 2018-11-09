bold=$(tput bold)
normal=$(tput sgr0)

echo "${bold}Testing Equivalent different implementations.${normal}"
echo "${bold}5 benchmarks total.${normal}"
echo "${bold}Total Expected Required Time: ~4 hours 20 minutes.${normal}"
echo ""

echo "${bold}Equivalent Implementation of SHA #1${normal}"
echo "${bold}Expected result: p1 is equivalent to p2${normal}"
echo "${bold}Expected Required Time: ~47 minutes${normal}"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm10 --p2lang asm --arch x86_64  --verif_mode hybrid --max_unknown_count 5
echo ""

echo "${bold}Equivalent Implementation of SHA #2${normal}"
echo "${bold}Expected result: p1 is equivalent to p2${normal}"
echo "${bold}Expected Required Time: ~53 minutes${normal}"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm11 --p2lang asm --arch x86_64  --verif_mode hybrid --max_unknown_count 5
echo ""

echo "${bold}Equivalent Implementation of SHA #3${normal}"
echo "${bold}Expected result: p1 is equivalent to p2${normal}"
echo "${bold}Expected Required Time: ~47 minutes${normal}"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm12 --p2lang asm --arch x86_64  --verif_mode hybrid --max_unknown_count 5
echo ""

echo "${bold}Equivalent Implementation of SHA #4${normal}"
echo "${bold}Expected result: p1 is equivalent to p2${normal}"
echo "${bold}Expected Required Time: ~53 minutes${normal}"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm13 --p2lang asm --arch x86_64  --verif_mode hybrid --max_unknown_count 5
echo ""

echo "${bold}Equivalent Implementation of SHA #5${normal}"
echo "${bold}Expected result: p1 is equivalent to p2${normal}"
echo "${bold}Expected Required Time: ~1 hour${normal}"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm14 --p2lang asm --arch x86_64  --verif_mode hybrid --max_unknown_count 5
echo ""
