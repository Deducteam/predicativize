all:
	dune build

test_with_optim:
	time dune exec -- predicativize -s -o arith_fermat_noleibniz/connectives.dk arith_fermat_noleibniz/leibniz.dk arith_fermat_noleibniz/logic.dk arith_fermat_noleibniz/relations.dk arith_fermat_noleibniz/bool.dk arith_fermat_noleibniz/nat.dk arith_fermat_noleibniz/fact.dk arith_fermat_noleibniz/div_mod.dk arith_fermat_noleibniz/bigops.dk arith_fermat_noleibniz/primes.dk arith_fermat_noleibniz/cong.dk arith_fermat_noleibniz/exp.dk arith_fermat_noleibniz/gcd.dk arith_fermat_noleibniz/permutation.dk arith_fermat_noleibniz/sigma_pi.dk arith_fermat_noleibniz/fermat.dk

test:
	time dune exec -- predicativize -s arith_fermat/connectives.dk arith_fermat/leibniz.dk arith_fermat/logic.dk arith_fermat/relations.dk arith_fermat/bool.dk arith_fermat/nat.dk arith_fermat/fact.dk arith_fermat/div_mod.dk arith_fermat/bigops.dk arith_fermat/primes.dk arith_fermat/cong.dk arith_fermat/exp.dk arith_fermat/gcd.dk arith_fermat/permutation.dk arith_fermat/sigma_pi.dk arith_fermat/fermat.dk
