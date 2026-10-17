for d in L D1 SA W7 R3; do
  python3 ref_enc.py ctrl_drop$d.cnf drop=$d > ctrl_drop$d.log 2>&1
  timeout 600 python3 ref_solve.py ctrl_drop$d.cnf glucose4 noproof >> ctrl_drop$d.log 2>&1
  [ -f ctrl_drop$d.cnf.glucose4.model ] && python3 ref_check.py ctrl_drop$d.cnf >> ctrl_drop$d.log 2>&1
  rm -f ctrl_drop$d.cnf
done
echo DONE > ctrl.done
