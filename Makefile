all:
	dune build

test_with_optim:
	dkcheck -e -I theory theory/sttfa.dk
	time dune exec -- predicativize --meta metas/sttfa_to_pts.dk -o arith_fermat_noleibniz/connectives.dk arith_fermat_noleibniz/leibniz.dk arith_fermat_noleibniz/logic.dk arith_fermat_noleibniz/relations.dk arith_fermat_noleibniz/bool.dk arith_fermat_noleibniz/nat.dk arith_fermat_noleibniz/fact.dk arith_fermat_noleibniz/div_mod.dk arith_fermat_noleibniz/bigops.dk arith_fermat_noleibniz/primes.dk arith_fermat_noleibniz/cong.dk arith_fermat_noleibniz/exp.dk arith_fermat_noleibniz/gcd.dk arith_fermat_noleibniz/permutation.dk arith_fermat_noleibniz/sigma_pi.dk arith_fermat_noleibniz/fermat.dk

test_with_optim_agda:
	dkcheck -e -I theory theory/sttfa.dk
	time dune exec -- predicativize --meta metas/sttfa_to_pts.dk -o -a arith_fermat_noleibniz/connectives.dk arith_fermat_noleibniz/leibniz.dk arith_fermat_noleibniz/logic.dk arith_fermat_noleibniz/relations.dk arith_fermat_noleibniz/bool.dk arith_fermat_noleibniz/nat.dk arith_fermat_noleibniz/fact.dk arith_fermat_noleibniz/div_mod.dk arith_fermat_noleibniz/bigops.dk arith_fermat_noleibniz/primes.dk arith_fermat_noleibniz/cong.dk arith_fermat_noleibniz/exp.dk arith_fermat_noleibniz/gcd.dk arith_fermat_noleibniz/permutation.dk arith_fermat_noleibniz/sigma_pi.dk arith_fermat_noleibniz/fermat.dk


test:
	dkcheck -e -I theory theory/sttfa.dk
	time dune exec -- predicativize --meta metas/sttfa_to_pts.dk arith_fermat/connectives.dk arith_fermat/leibniz.dk arith_fermat/logic.dk arith_fermat/relations.dk arith_fermat/bool.dk arith_fermat/nat.dk arith_fermat/fact.dk arith_fermat/div_mod.dk arith_fermat/bigops.dk arith_fermat/primes.dk arith_fermat/cong.dk arith_fermat/exp.dk arith_fermat/gcd.dk arith_fermat/permutation.dk arith_fermat/sigma_pi.dk arith_fermat/fermat.dk

test_agda:
	dkcheck -e -I theory theory/sttfa.dk
	time dune exec -- predicativize --meta metas/sttfa_to_pts.dk -a arith_fermat/connectives.dk arith_fermat/leibniz.dk arith_fermat/logic.dk arith_fermat/relations.dk arith_fermat/bool.dk arith_fermat/nat.dk arith_fermat/fact.dk arith_fermat/div_mod.dk arith_fermat/bigops.dk arith_fermat/primes.dk arith_fermat/cong.dk arith_fermat/exp.dk arith_fermat/gcd.dk arith_fermat/permutation.dk arith_fermat/sigma_pi.dk arith_fermat/fermat.dk

.PHONY: matita
matita:
	dkcheck -e -I theory/matita/meta theory/matita/meta/cic.dk theory/matita/meta/univs.dk
	dkcheck -e -I theory/matita theory/matita/cic.dk theory/matita/univs.dk
	dune exec -- predicativize --meta metas/matita_to_pts.dk --path theory/matita/meta/ --cstr extra_cstrs/matita.dk matita/matita_basics_logic.dk matita/matita_basics_relations.dk matita/matita_basics_bool.dk matita/matita_arithmetics_nat.dk matita/matita_arithmetics_div_and_mod.dk matita/matita_arithmetics_exp.dk matita/matita_arithmetics_factorial.dk matita/matita_arithmetics_minimization.dk matita/matita_arithmetics_primes.dk matita/matita_arithmetics_congruence.dk matita/matita_arithmetics_gcd.dk matita/matita_arithmetics_chinese_reminder.dk matita/matita_basics_types.dk matita/matita_arithmetics_bigops.dk matita/matita_arithmetics_log.dk matita/matita_arithmetics_sigma_pi.dk matita/matita_arithmetics_chebyshev_chebyshev_psi.dk matita/matita_arithmetics_ord.dk matita/matita_arithmetics_chebyshev_factorization.dk matita/matita_arithmetics_bounded_quantifiers.dk matita/matita_arithmetics_permutation.dk matita/matita_arithmetics_lstar.dk matita/matita_arithmetics_sqrt.dk matita/matita_arithmetics_binomial.dk matita/matita_arithmetics_chebyshev_chebyshev_theta.dk matita/matita_arithmetics_chebyshev_psi_bounds.dk matita/matita_arithmetics_chebyshev_bertrand.dk matita/matita_basics_lists_list.dk matita/matita_arithmetics_chebyshev_bertrand256.dk matita/matita_arithmetics_fermat_little_theorem.dk  matita/matita_arithmetics_pidgeon_hole.dk  matita/matita_arithmetics_iteration.dk
