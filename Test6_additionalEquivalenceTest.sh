echo "Correctly Mutated SHA256 #1"
echo "Expected Result - Equivalent"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm10 --p2lang asm --arch x86_64  --verif_mode hybrid --max_unknown_count 5

echo "Correctly Mutated SHA256 #2"
echo "Expected Result - Equivalent"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm11 --p2lang asm --arch x86_64  --verif_mode hybrid --max_unknown_count 5

echo "Correctly Mutated SHA256 #3"
echo "Expected Result - Equivalent"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm12 --p2lang asm --arch x86_64  --verif_mode hybrid --max_unknown_count 5

echo "Correctly Mutated SHA256 #4"
echo "Expected Result - Equivalent"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm13 --p2lang asm --arch x86_64  --verif_mode hybrid --max_unknown_count 5

echo "Correctly Mutated SHA256 #5"
echo "Expected Result - Equivalent"
time python3 main.py --pre test/sha256/pre --post test/sha256/post --p1 test/sha256/dsl --p1lang dsl --p2 test/sha256/diffInst/asm14 --p2lang asm --arch x86_64  --verif_mode hybrid --max_unknown_count 5
