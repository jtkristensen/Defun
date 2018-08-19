# All tests are done by visual inspection.
# Does all programs return the correct thing or not.

src=./input_programs
dst=./output_programs

function rhs {
    stack runhaskell -- ./defun-code.hs $1 $2
}
function doone {
    rhs -$1 $src/$2.pcf > $dst/$1_$2.sml
}
function doall {
  doone $1 arithmetic  # Should return 16.
  doone $1 arithmetic1 # Should return 64.
  doone $1 fib         # Should return 89.
  doone $1 implicit    # Should return  2.
  doone $1 simple      # Should return  2.
  doone $1 simpler     # Should return 11.
  doone $1 conditional # Should return  1.
}

make clean
doall cfa
doall naive

for p in $(ls $dst); do
    mosml $dst/$p
done

# Demonstrating simple dead code-detection
# as a biproduct of the control-flow analysis.
doone cfa dead_fun
less ./output_programs/cfa_dead_fun.sml

