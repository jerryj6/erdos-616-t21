cd work/e616/t21
for ac in "2 3" "3 2" "2 4" "3 3" "3 4"; do timeout 900 python3 w6caseN.py $ac 9 120; done
