.PHONY: matita matita_agda test test_agda test_with_optim test_with_optim_agda

all:
	dune build

test_with_optim:
	dkcheck -e -I theory theory/sttfa.dk
	time dune exec -- predicativize --path theory --meta metas/sttfa_to_pts.dk -o input/arith_fermat_noleibniz/connectives.dk input/arith_fermat_noleibniz/leibniz.dk input/arith_fermat_noleibniz/logic.dk input/arith_fermat_noleibniz/relations.dk input/arith_fermat_noleibniz/bool.dk input/arith_fermat_noleibniz/nat.dk input/arith_fermat_noleibniz/fact.dk input/arith_fermat_noleibniz/div_mod.dk input/arith_fermat_noleibniz/bigops.dk input/arith_fermat_noleibniz/primes.dk input/arith_fermat_noleibniz/cong.dk input/arith_fermat_noleibniz/exp.dk input/arith_fermat_noleibniz/gcd.dk input/arith_fermat_noleibniz/permutation.dk input/arith_fermat_noleibniz/sigma_pi.dk input/arith_fermat_noleibniz/fermat.dk


test_with_optim_agda:
	dkcheck -e -I theory theory/sttfa.dk
	time dune exec -- predicativize -a --path theory --meta metas/sttfa_to_pts.dk -o input/arith_fermat_noleibniz/connectives.dk input/arith_fermat_noleibniz/leibniz.dk input/arith_fermat_noleibniz/logic.dk input/arith_fermat_noleibniz/relations.dk input/arith_fermat_noleibniz/bool.dk input/arith_fermat_noleibniz/nat.dk input/arith_fermat_noleibniz/fact.dk input/arith_fermat_noleibniz/div_mod.dk input/arith_fermat_noleibniz/bigops.dk input/arith_fermat_noleibniz/primes.dk input/arith_fermat_noleibniz/cong.dk input/arith_fermat_noleibniz/exp.dk input/arith_fermat_noleibniz/gcd.dk input/arith_fermat_noleibniz/permutation.dk input/arith_fermat_noleibniz/sigma_pi.dk input/arith_fermat_noleibniz/fermat.dk

isabelle_agda:
	dkcheck -e -I theory theory/sttfa.dk
	time dune exec -- predicativize -a --meta metas/sttfa_to_pts.dk --path theory --eta input/isabelle_sttfa.dk

test:
	dkcheck -e -I theory theory/sttfa.dk
	time dune exec -- predicativize --meta metas/sttfa_to_pts.dk --path theory input/arith_fermat/connectives.dk input/arith_fermat/leibniz.dk input/arith_fermat/logic.dk input/arith_fermat/relations.dk input/arith_fermat/bool.dk input/arith_fermat/nat.dk input/arith_fermat/fact.dk input/arith_fermat/div_mod.dk input/arith_fermat/bigops.dk input/arith_fermat/primes.dk input/arith_fermat/cong.dk input/arith_fermat/exp.dk input/arith_fermat/gcd.dk input/arith_fermat/permutation.dk input/arith_fermat/sigma_pi.dk input/arith_fermat/fermat.dk


test_agda:
	dkcheck -e -I theory theory/sttfa.dk
	time dune exec -- predicativize -a --meta metas/sttfa_to_pts.dk --path theory input/arith_fermat/connectives.dk input/arith_fermat/leibniz.dk input/arith_fermat/logic.dk input/arith_fermat/relations.dk input/arith_fermat/bool.dk input/arith_fermat/nat.dk input/arith_fermat/fact.dk input/arith_fermat/div_mod.dk input/arith_fermat/bigops.dk input/arith_fermat/primes.dk input/arith_fermat/cong.dk input/arith_fermat/exp.dk input/arith_fermat/gcd.dk input/arith_fermat/permutation.dk input/arith_fermat/sigma_pi.dk input/arith_fermat/fermat.dk

running_example:
	dkcheck -e -I theory theory/sttfa.dk
	time dune exec -- predicativize -a --meta metas/sttfa_to_pts.dk --path theory input/running_example.dk


test_agda_with_typecheck:
	dkcheck -e -I theory theory/sttfa.dk
	time dune exec -- predicativize -at --meta metas/sttfa_to_pts.dk --path theory input/arith_fermat/connectives.dk input/arith_fermat/leibniz.dk input/arith_fermat/logic.dk input/arith_fermat/relations.dk input/arith_fermat/bool.dk input/arith_fermat/nat.dk input/arith_fermat/fact.dk input/arith_fermat/div_mod.dk input/arith_fermat/bigops.dk input/arith_fermat/primes.dk input/arith_fermat/cong.dk input/arith_fermat/exp.dk input/arith_fermat/gcd.dk input/arith_fermat/permutation.dk input/arith_fermat/sigma_pi.dk input/arith_fermat/fermat.dk


matita:
	dkcheck -e -I theory/matita/meta theory/matita/meta/cic.dk theory/matita/meta/univs.dk
	dkcheck -e -I theory/matita theory/matita/cic.dk theory/matita/univs.dk
	time dune exec -- predicativize --meta metas/matita_to_pts.dk --path theory/matita/meta/ --path theory --cstr extra_cstrs/matita.dk input/matita/matita_basics_logic.dk input/matita/matita_basics_relations.dk input/matita/matita_basics_bool.dk input/matita/matita_arithmetics_nat.dk input/matita/matita_arithmetics_div_and_mod.dk input/matita/matita_arithmetics_exp.dk input/matita/matita_arithmetics_factorial.dk input/matita/matita_arithmetics_minimization.dk input/matita/matita_arithmetics_primes.dk input/matita/matita_arithmetics_congruence.dk input/matita/matita_arithmetics_gcd.dk input/matita/matita_arithmetics_chinese_reminder.dk input/matita/matita_arithmetics_lstar.dk input/matita/matita_arithmetics_log.dk input/matita/matita_arithmetics_sqrt.dk input/matita/matita_basics_types.dk input/matita/matita_arithmetics_bigops.dk input/matita/matita_arithmetics_sigma_pi.dk input/matita/matita_arithmetics_chebyshev_chebyshev_psi.dk input/matita/matita_arithmetics_binomial.dk input/matita/matita_arithmetics_chebyshev_chebyshev_theta.dk input/matita/matita_arithmetics_ord.dk input/matita/matita_arithmetics_chebyshev_factorization.dk input/matita/matita_arithmetics_chebyshev_psi_bounds.dk input/matita/matita_arithmetics_chebyshev_bertrand.dk input/matita/matita_basics_lists_list.dk input/matita/matita_arithmetics_chebyshev_bertrand256.dk input/matita/matita_arithmetics_permutation.dk input/matita/matita_arithmetics_fermat_little_theorem.dk input/matita/matita_arithmetics_iteration.dk input/matita/matita_arithmetics_bounded_quantifiers.dk input/matita/matita_arithmetics_pidgeon_hole.dk


matita_agda:
	dkcheck -e -I theory/matita/meta theory/matita/meta/cic.dk theory/matita/meta/univs.dk
	dkcheck -e -I theory/matita theory/matita/cic.dk theory/matita/univs.dk
	time dune exec -- predicativize -a --meta metas/matita_to_pts.dk --path theory/matita/meta/ --path theory --cstr extra_cstrs/matita.dk input/matita/matita_basics_logic.dk input/matita/matita_basics_relations.dk input/matita/matita_basics_bool.dk input/matita/matita_arithmetics_nat.dk input/matita/matita_arithmetics_div_and_mod.dk input/matita/matita_arithmetics_exp.dk input/matita/matita_arithmetics_factorial.dk input/matita/matita_arithmetics_minimization.dk input/matita/matita_arithmetics_primes.dk input/matita/matita_arithmetics_congruence.dk input/matita/matita_arithmetics_gcd.dk input/matita/matita_arithmetics_chinese_reminder.dk input/matita/matita_arithmetics_lstar.dk input/matita/matita_arithmetics_log.dk input/matita/matita_arithmetics_sqrt.dk input/matita/matita_basics_types.dk input/matita/matita_arithmetics_bigops.dk input/matita/matita_arithmetics_sigma_pi.dk input/matita/matita_arithmetics_chebyshev_chebyshev_psi.dk input/matita/matita_arithmetics_binomial.dk input/matita/matita_arithmetics_chebyshev_chebyshev_theta.dk input/matita/matita_arithmetics_ord.dk input/matita/matita_arithmetics_chebyshev_factorization.dk input/matita/matita_arithmetics_chebyshev_psi_bounds.dk input/matita/matita_arithmetics_chebyshev_bertrand.dk input/matita/matita_basics_lists_list.dk input/matita/matita_arithmetics_chebyshev_bertrand256.dk input/matita/matita_arithmetics_permutation.dk input/matita/matita_arithmetics_fermat_little_theorem.dk input/matita/matita_arithmetics_iteration.dk input/matita/matita_arithmetics_bounded_quantifiers.dk input/matita/matita_arithmetics_pidgeon_hole.dk
