theory LeapingFrog
  imports Main HOL.Real HOL.NthRoot HOL.Boolean_Algebras HOL.Series
begin

definition w :: "real" where
"w = (sqrt 5 - 1)/2"

lemma w_squared: "w^2 = 1 - w"
proof -
  have "w^2 = (sqrt 5 - 1)^2 / 4"
    by (simp add: w_def power_divide)
  moreover have "(sqrt 5 - 1)^2 = (sqrt 5)^2 - 2*(sqrt 5)*1 + 1^2"
    by (simp add: power2_diff)
  ultimately have w_squared: "w^2 = (3 - (sqrt 5))/2" by force
  moreover have "1 - w = (3 - sqrt(5))/2" using w_def by auto
  ultimately show "w^2 = 1 - w" by force
qed

lemma w_range: "w > 0 \<and> w < 1"
proof -
  have "sqrt 5 > 1" by force
  then have 1: "w > 0" by (simp add: w_def)
  have "w^2 < 1" using w_def w_squared using 1 by linarith
  then have 2: "w < 1" by (smt (verit) one_le_power)
  then show ?thesis using 1 2 by blast
qed

lemma w_recurrence: "w^(n+1) + w^(n+2) = w^n"
proof -
  have "w^(n+1) + w^(n+2) = w^n*(w + w^2)"
    by (smt (verit) power_add power_one_right right_diff_distrib)
  moreover have "w + w^2 = 1" using w_squared by simp
  ultimately show ?thesis by simp
qed

type_synonym position = "(int \<times> nat)"
type_synonym coins = "position set"

inductive jump :: "coins \<Rightarrow> coins \<Rightarrow> bool" where
  left: "\<lbrakk>(x,y) \<in> A; (x-1, y) \<in> A; (x-2, y) \<notin> A; B = (A - {(x,y), (x-1,y)}) \<union> {(x-2, y)}\<rbrakk>
    \<Longrightarrow> jump A B"
| right: "\<lbrakk>(x,y) \<in> A; (x+1, y) \<in> A; (x+2, y) \<notin> A; B = (A - {(x,y), (x+1,y)}) \<union> {(x+2, y)}\<rbrakk>
    \<Longrightarrow> jump A B"
| up: "\<lbrakk>(x,y) \<in> A; (x, y-1) \<in> A; (x, y-2) \<notin> A; B = (A - {(x,y), (x,y-1)}) \<union> {(x, y-2)}\<rbrakk>
    \<Longrightarrow> jump A B"
| down: "\<lbrakk>(x,y) \<in> A; (x, y+1) \<in> A; (x, y+2) \<notin> A; B = (A - {(x,y), (x,y+1)}) \<union> {(x, y+2)}\<rbrakk>
    \<Longrightarrow> jump A B"

lemma example_right: "jump {(0, 0), (1, 0)} {(2, 0)}" using jump.right[of 0 0]
  by (smt (verit, ccfv_SIG) Diff_cancel Diff_iff Un_Diff_cancel Un_Diff_cancel2 insert_iff prod.inject sup_bot.right_neutral)
lemma example_left: "jump {(0, 0), (-1, 0)} {(-2, 0)}" using jump.left[of 0 0]
  by (smt (z3) Diff_cancel Un_Diff_cancel2 insertCI insertE insert_absorb insert_is_Un insert_not_empty prod.inject)
lemma example_up: "jump {(0, 2), (0, 1)} {(0, 0)}" using jump.up[of 0 2]
  by (metis Diff_cancel One_nat_def Un_Diff_cancel2 add_diff_cancel_left' insert_absorb insert_iff insert_is_Un insert_not_empty nat_1_add_1 plus_1_eq_Suc plus_nat.simps(2) prod.inject zero_neq_numeral)
lemma example_down: "jump {(0, 0), (0, 1)} {(0, 2)}" using jump.down[of 0 0]
  by (metis (no_types, lifting) Diff_cancel One_nat_def Un_Diff_cancel2 add.commute insert_absorb insert_iff insert_is_Un insert_not_empty nat_1_add_1 one_eq_numeral_iff plus_1_eq_Suc plus_nat.simps(2) prod.inject semiring_norm(85) zero_neq_numeral)

definition "symm_diff" (infix \<open>\<triangle>\<close> 70) where
"symm_diff A B = (A - B) \<union> (B - A)"

value "{1::int,2,3} \<triangle> {3,4,5}"

lemma symm_diff_eq: "c \<in> A \<triangle> B \<longleftrightarrow> (c \<in> A \<and> c \<notin> B) \<or> (c \<in> B \<and> c \<notin> A)" (is "?lhs \<longleftrightarrow> ?rhs")
  by (metis Diff_iff Un_iff symm_diff_def)

lemma "jump c1 c2 \<longleftrightarrow> (\<exists>x y. c1 \<triangle> c2 = {(x,y), (x,y+1), (x,y+2)} \<or> c1 \<triangle> c2 = {(x,y), (x+1,y), (x+2,y)})" (is "?lhs \<longleftrightarrow> ?rhs")
  sorry
(* proof assume "?lhs"
  then show "?rhs" proof (cases rule: jump.cases)
    case (left x y) (*from left have "c1 - c2 \<supseteq> {(x, y), (x-1, y)}" sorry by auto *)
    then have "c1 \<triangle> c2 = {(x, y), (x-1, y), (x-2, y)}" apply (rule set_eqI)
    then show ?thesis sorry  next
    case (right x y) then show ?thesis sorry
  next case (up x y) then show ?thesis sorry
  next case (down x y) then show ?thesis sorry
  qed qed *)

fun below_the_line :: "position \<Rightarrow> bool" where
"below_the_line (_, y) = (y \<ge> 5)"

definition initial_coins :: "coins \<Rightarrow> bool" where
"initial_coins coins \<longleftrightarrow> (\<forall>coin \<in> coins. below_the_line coin)"

definition max_initial_coins :: "coins" where
"max_initial_coins = {(x, y) |x y. y \<ge> 5}" 

definition all_coins :: "coins" where
"all_coins = {(x,y)|x y. True}"

lemma initial_coins_subset: "initial_coins coins \<Longrightarrow> coins \<subseteq> max_initial_coins"
  using initial_coins_def max_initial_coins_def by fastforce

fun point_pow :: "coins \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
"point_pow c x y = (if (int(x), y) \<in> c then w^(x+y) else 0)
  + (if (-int(x), y) \<in> c \<and> x > 0 then w^(x+y) else 0)"

fun power_sum :: "coins \<Rightarrow> real" where
"power_sum c = suminf (\<lambda>x. suminf (point_pow c x))"
            
(* lemmas finite_tuple_induct = finite_induct[split_format(complete)] *)

lemma series_one_term_different:
  assumes f_g_diff: "(g :: nat \<Rightarrow> real) (k::nat) = f k + d"
      and f_g_eq: "\<And>i. i \<noteq> k \<Longrightarrow> f i = g i"
      and "summable f"
    shows "suminf g = suminf f + d"
proof -
  have f_initsum:  "(\<lambda>i. f (i + (k+1))) sums s \<longleftrightarrow> f sums (s + (\<Sum>i<k+1. f i))" 
    for s using sums_iff_shift by blast
  have g_initsum:  "(\<lambda>i. g (i + (k+1))) sums s \<longleftrightarrow> g sums (s + (\<Sum>i<k+1. g i))" 
    for s using sums_iff_shift by blast
  have init_diff: "(\<Sum>i<k+1. g i) = (\<Sum>i<k+1. f i) + d"
  proof -
    have "(\<Sum>i<k+1. g i) = (\<Sum>i<k. g i) + g k" by simp
    moreover have "(\<Sum>i<k+1. f i) = (\<Sum>i<k. f i) + f k" by simp
    moreover have "(\<Sum>i<k. g i) = (\<Sum>i<k. f i)" using f_g_eq by simp
    ultimately show ?thesis using f_g_diff by simp
  qed
  have tails_eq: "(\<lambda>i. f (i + (k+1))) = (\<lambda>i. g (i + (k+1)))" using f_g_eq by simp
  have "f sums s \<Longrightarrow> g sums (s + d)" for s
  proof -
    assume "f sums s"
    then have "(\<lambda>i. f (i + (k+1))) sums (s - (\<Sum>i<k+1. f i))"
      using f_initsum by auto
    then have "(\<lambda>i. f (i + (k+1))) sums (s - (\<Sum>i<k+1. f i))"
      using tails_eq by simp
    then have "(\<lambda>i. f (i + (k+1))) sums (s - ((\<Sum>i<k+1. g i) - d))"
      using init_diff by simp
    then show "g sums (s + d)" using g_initsum tails_eq by simp
  qed
  then show ?thesis using \<open>summable f\<close> sums_iff by blast
qed

(* We could show the following lemmas... however let's wait if we really need them.
   TODO we do! *)

lemma point_pow_summable: "summable (point_pow coins x)" 
proof -
  have summable_all: "summable (point_pow all_coins 0)" sorry
  let ?f0 = "point_pow all_coins 0"
  (* have "?f0 sums todo" *)

  have point_pow_leq: "point_pow all_coins x \<le> point_pow all_coins 0" sorry
  have "summable (point_pow all_coins x)" using summable_all point_pow_leq sorry
  show ?thesis sorry
qed

lemma power_sum_summable: "summable (\<lambda>x. suminf (point_pow coins x))" sorry

lemma power_sum_union_singleton:
  "(x,y) \<notin> F \<Longrightarrow> power_sum (F \<union> {(x,y)}) = power_sum F + w^(nat (abs x) + y)"
proof -
  assume notinF: "(x,y) \<notin> F"
  let ?Fnew = "insert (x,y) F"
  let ?x = "nat (abs x)"
  have otherx: "x' \<noteq> ?x \<Longrightarrow> suminf (point_pow ?Fnew x') = suminf (point_pow F x')" for x'
  proof -
    assume xneq: "x' \<noteq> ?x"
    from xneq have poseq: "(x', y) \<in> F \<longleftrightarrow> (x', y) \<in> ?Fnew" by fastforce
    from xneq have negeq: "(-x', y) \<in> F \<longleftrightarrow> (-x', y) \<in> ?Fnew" by fastforce
    from poseq negeq show ?thesis by (smt (verit, ccfv_threshold) Pair_inject case_prod_conv
          insert_iff point_pow.elims suminf_cong notinF)
  qed

  (*
      |
    ------
    -xx---
    -xx0--
    --xxx
    
    F =     {(-1,1), (0,1), (-1,2), (0,2),        (0,3), (1,3), (2,3)}
    ?Fnew = {(-1,1), (0,1), (-1,2), (0,2), (1,2), (0,3), (1,3), (2,3)}
    
    Sum_y point_pow F x' y = Sum_y point_pow ?Fnew x' y for all x' in {0, 2, 3, ...}
    For x = 1:        point_pow F x y = point_pow ?Fnew x y for all y in {0, 1, 3, 4, ...}
    For x = 1, y = 2: point_pow ?Fnew x y = point_pow F x y + w^(x+y)
  *)

  have othery: "y' \<noteq> y \<Longrightarrow> point_pow ?Fnew ?x y' = point_pow F ?x y'" for y'
  proof -
    assume yneq: "y' \<noteq> y"
    from yneq have yinFeq: "(x', y') \<in> F \<longleftrightarrow> (x', y') \<in> ?Fnew" for x'  by simp
    from this show ?thesis by force
  qed

  have samexy: "point_pow ?Fnew ?x y = point_pow F ?x y + w^(?x+y)"
  proof (cases "(x, y) \<in> F")
    case True
    then show ?thesis using notinF by fastforce
  next
    case False
    then show ?thesis proof (cases "(-x, y) \<in> F")
      case True
      then show ?thesis
        by (smt (verit, ccfv_SIG) notinF insertCI nat_0_le point_pow.elims zero_less_nat_eq)
    next
      case False
      then show ?thesis
        by (smt (verit, del_insts) notinF insert_iff int_nat_eq point_pow.elims prod.inject zero_less_nat_eq)
    qed
  qed

  have samex: "suminf (point_pow ?Fnew ?x) = suminf (point_pow F ?x) + w^(?x+y)"
    using series_one_term_different samexy othery point_pow_summable by presburger


  have "suminf (\<lambda>x. suminf (point_pow ?Fnew x)) = suminf (\<lambda>x. suminf (point_pow F x)) + w^(?x+y)"
    using series_one_term_different samex otherx power_sum_summable by presburger
  then show ?thesis by simp
qed

corollary power_sum_minus_singleton:
  "(x,y) \<in> F \<Longrightarrow> power_sum (F - {(x,y)}) = power_sum F - w^(nat (abs x) + y)"
  using mk_disjoint_insert power_sum_union_singleton by fastforce

lemma finite_power_sum:
  assumes finite: "finite coins"
  shows "power_sum coins = sum (\<lambda>(x,y). w ^ (nat (abs x) + y)) coins"
using finite proof (induction coins)
  case empty
  have "point_pow {} x y = 0" for x y by simp
  then have "suminf (point_pow {} x) = 0" for x by (metis sums_0 sums_unique)
  then show ?case by simp
next
  case (insert t F)
  then obtain x y where xy: "t = (x, y)" by (meson surj_pair)
  have 1: "power_sum (insert t F) = power_sum F + w^(nat (abs x) + y)"
    using insert.hyps(2) power_sum_union_singleton xy by fastforce
  have 2: "sum (\<lambda>(x,y). w ^ (nat (abs x) + y)) (insert t F)
    = sum (\<lambda>(x,y). w ^ (nat (abs x) + y)) F + w^(nat (abs x) + y)" using insert xy by force
  from 1 2 insert show ?case by simp
qed

corollary goal_field_value_1: "power_sum {(0,0)} = 1"
  using finite_power_sum by simp

lemma point_pow_subset_leq: "A \<subseteq> B \<Longrightarrow> point_pow A x y \<le> point_pow B x y"
  using w_range by auto

lemma powersum_inner_subset_leq: "A \<subseteq> B \<Longrightarrow> suminf (point_pow A x) \<le> suminf (point_pow B x)"
  by (meson point_pow_subset_leq point_pow_summable suminf_le)

lemma powersum_subset_leq:
  "A \<subseteq> B \<Longrightarrow> power_sum A \<le> power_sum B"
proof -
  assume "A \<subseteq> B"
  then have "\<lbrakk>(\<lambda>x. suminf (point_pow A x)) sums s; (\<lambda>x. suminf (point_pow B x)) sums t\<rbrakk>
    \<Longrightarrow> s \<le> t" for s t by (metis (full_types) sums_le powersum_inner_subset_leq)
  then show ?thesis by (simp add: power_sum_summable summable_sums)
qed

lemma point_pow_subset_less: "A \<subseteq> B \<and> (x,y) \<in> B - A 
    \<Longrightarrow> point_pow A (nat (abs x)) y < point_pow B (nat (abs x)) y"
  by (smt (verit, best) DiffD2 Diff_partition Un_iff nat_eq_iff point_pow.elims w_range
        zero_less_nat_eq zero_less_power)

(* TODO remove if not needed? But may be needed for point_pow_summable etc. *)
lemma summable_nonneg_comparison_test:
  assumes f_summable: "summable (f::nat \<Rightarrow> real)"
      and f_dom_g: "\<And>i. g i \<le> f i"
      and nonneg: "\<And>i. 0 \<le> g i"
shows "summable g"
proof -
  have "\<forall>n. norm (g n) \<le> f n" by (simp add: f_dom_g nonneg)
  then show ?thesis using summable_comparison_test f_summable by blast
qed

lemma powersum_subset_less:
  "A \<subset> B \<Longrightarrow> power_sum A < power_sum B"
proof -
  assume subset: "A \<subset> B"
  then obtain x y where xy: "(x,y) \<in> B - A" by auto
  let ?x = "nat (abs x)"

  have "point_pow B ?x y - point_pow A ?x y > 0" using xy point_pow_subset_less
    by (simp add: order_less_imp_le subset)
  moreover have "summable (\<lambda>y. point_pow B ?x y - point_pow A ?x y)"
    using point_pow_summable summable_diff by blast
  ultimately have "suminf (\<lambda>y. point_pow B ?x y - point_pow A ?x y) > 0"
    by (smt (verit) order_less_imp_le point_pow_subset_leq subset suminf_pos_iff)

  moreover have "suminf (\<lambda>y. point_pow B ?x y - point_pow A ?x y)
    = suminf (point_pow B ?x) - suminf (point_pow A ?x)" 
    using suminf_diff[of "point_pow B ?x" "point_pow A ?x"] point_pow_summable by simp
  ultimately have "suminf (point_pow B ?x) - suminf (point_pow A ?x) > 0" by simp
  moreover have "suminf (point_pow B x) - suminf (point_pow A x) \<ge> 0" for x
    by (simp add: order_less_imp_le powersum_inner_subset_leq subset)
  moreover have "summable (\<lambda>x. suminf (point_pow B x) - suminf (point_pow A x))"
    by (simp add: power_sum_summable summable_diff)
  ultimately have "suminf (\<lambda>x. suminf (point_pow B x) - suminf (point_pow A x)) > 0" 
    using suminf_pos_iff[where f="(\<lambda>x. suminf (point_pow B x) - suminf (point_pow A x))"] by blast
  then have "suminf (\<lambda>x. suminf (point_pow B x)) - suminf (\<lambda>x. suminf (point_pow A x)) > 0" 
    using suminf_diff[of "(\<lambda>x. suminf (point_pow B x))" "(\<lambda>x. suminf (point_pow A x))"]
          power_sum_summable by presburger
  then show ?thesis by simp
qed

(* kind of specific lemma, but an argument of this form
   is needed quite often in the following
*)
lemma geometric_sum_transformation: "(\<lambda>y. w^y) sums s \<Longrightarrow> (\<lambda>y. c*w^(a+y)) sums (c*w^(a)*s)"
proof -
  assume "(\<lambda>y. w^y) sums s"
  then have sum_unfold: "(\<lambda>n. \<Sum>i<n. (\<lambda>y. w^y) i) \<longlonglongrightarrow> s" by (simp add: sums_def)
  have "(\<lambda>_. c*w^a) \<longlonglongrightarrow> c*w^a" by simp
  from this sum_unfold have 
    "(\<lambda>n. c*w^a * (\<Sum>i<n. (\<lambda>y. w^y) i)) \<longlonglongrightarrow> c*w^a * s"
    using tendsto_mult by blast
  moreover have "c*w^a * (\<Sum>i<(n::nat). (\<lambda>y. w^y) i) 
      = (\<Sum>i<n. (\<lambda>y. c*w^a * w^y) i)" for n
    using sum_distrib_left by blast
  moreover have "(\<Sum>i<n. (\<lambda>y. c*w^a * w^y) i) = (\<Sum>i<n. (\<lambda>y. c*w^(a+y)) i)"
    for n by (metis ab_semigroup_mult_class.mult_ac(1) power_add)
  ultimately have "(\<lambda>n. (\<Sum>i<n. (\<lambda>y. c*w^(a+y)) i)) \<longlonglongrightarrow> c*w^a * s" by simp
  (*moreover have "x+5+y = x+y+5" for y by simp
  ultimately have "(\<lambda>n. (\<Sum>i<n. (\<lambda>y. 2*w^(x+y+5)) i)) \<longlonglongrightarrow> 2*w^(x+5) * s" by simp*)
  then have "(\<lambda>y. c*w^(a+y)) sums (c*w^a * s)" by (simp add: sums_def)
  then show ?thesis by simp
qed

theorem max_initial_coins_eq_one: "power_sum max_initial_coins = 1"
proof -
  have "norm w < 1" using w_range by auto
  then have "(\<lambda>n. w^n) sums (1/(1-w))" using geometric_sums by blast
  then have w_geometric_sum: "(\<lambda>n. w^n) sums (1/(w^2))" using w_squared by simp

  have x_eq_0: "x = 0 \<Longrightarrow> suminf (point_pow max_initial_coins x) = w^3" for x
  proof -
    assume "x = 0"
    have point_pow_unfold: "point_pow max_initial_coins x y = (if y \<ge> 5 then w^y else 0)" for y
      by (simp add: \<open>x = 0\<close> max_initial_coins_def)
    let ?f = "(\<lambda>y. (if y \<ge> 5 then w^y else 0))"

    have 1: "(\<lambda>y. w^(y+5)) sums s \<Longrightarrow> ?f sums s" for s
    proof -
      assume "(\<lambda>y. w^(y+5)) sums s"
      then have "(\<lambda>y. ?f (y + 5)) sums s" using le_add2 by presburger
      then have "?f sums (s + (\<Sum>i<5. ?f i))" using sums_iff_shift by blast
      then have "?f sums s" by simp
      then show ?thesis by simp
    qed

    have "(\<lambda>y. w^y) sums s \<Longrightarrow> (\<lambda>y. w^(5+y)) sums (w^5*s)" for s
      using geometric_sum_transformation[where c=1 and a=5] by simp
    then have 2: "(\<lambda>y. w^y) sums s \<Longrightarrow> (\<lambda>y. w^(y+5)) sums (w^5*s)" for s
      by (metis (no_types, lifting) Groups.add_ac(2) sums_cong)

    from 2 w_geometric_sum have "(\<lambda>y. w^(y+5)) sums (w^5/w^2)" by fastforce
    then have "(\<lambda>y. w^(y+5)) sums w^3" (* wtf... *)
      by (smt (z3) One_nat_def add_diff_cancel_right' le_add2 nat_1_add_1 numeral_3_eq_3 plus_1_eq_Suc power_Suc power_diff power_numeral_odd power_one_right times_divide_eq_left w_squared zero_power2)
    from this 1 have "?f sums w^3" by simp
    from this show ?thesis
      by (smt (verit, best) point_pow_unfold suminf_cong sums_unique)
  qed

  have x_ge_0: "x > 0 \<Longrightarrow> suminf (point_pow max_initial_coins x) = 2*w^(x+3)" for x
  proof -
    assume "x > 0"
    have point_pow_unfold: "point_pow max_initial_coins x y = (if y \<ge> 5 then 2*w^(x+y) else 0)" for y
      by (simp add: \<open>x > 0\<close> max_initial_coins_def)
    let ?f = "(\<lambda>y. (if y \<ge> 5 then 2*w^(x+y) else 0))"

    have 1: "(\<lambda>y. 2*w^(x+y+5)) sums s \<Longrightarrow> ?f sums s" for s
    proof -
      assume "(\<lambda>y. 2*w^(x+y+5)) sums s"
      then have "(\<lambda>y. ?f (y + 5)) sums s" using le_add2
        by (smt (verit, ccfv_SIG) group_cancel.add1 sums_cong)
      then have "?f sums (s + (\<Sum>i<5. ?f i))" using sums_iff_shift by blast
      then have "?f sums s" by simp
      then show ?thesis by simp
    qed

    have "(\<lambda>y. w^y) sums s \<Longrightarrow> (\<lambda>y. 2*w^(x+5+y)) sums (2*w^(x+5)*s)" for s
      using geometric_sum_transformation by simp
    then have 2: "(\<lambda>y. w^y) sums s \<Longrightarrow> (\<lambda>y. 2*w^(x+y+5)) sums (2*w^(x+5)*s)" for s
      by (smt (verit) Groups.add_ac(2) group_cancel.add1 sums_cong)

    have "2 \<le> x+5" by simp
    then have "2*w^(x+5)/w^2 = 2*w^(x+5-2)" using power_diff
      by (smt (verit, ccfv_threshold) comm_semiring_class.distrib divide_eq_0_iff field_class.field_divide_inverse real_sqrt_eq_1_iff w_def)
    moreover have "x+5-2 = x+3" by simp
    ultimately have w_pow_diff: "2*w^(x+5)/w^2 = 2*w^(x+3)" by simp

    from 2 w_geometric_sum have "(\<lambda>y. 2*w^(x+y+5)) sums (2*w^(x+5)/w^2)" by fastforce
    from this w_pow_diff have "(\<lambda>y. 2*w^(x+y+5)) sums (2*w^(x+3))" by metis
    from this 1 have "?f sums (2*w^(x+3))" by blast
    from this show ?thesis
      by (smt (verit, best) point_pow_unfold suminf_cong sums_unique)
  qed

  from x_eq_0 x_ge_0 have x_inner_sum:
    "suminf (point_pow max_initial_coins x) = (if x = 0 then w^3 else 2*w^(x+3))" for x by simp

  show ?thesis
  proof -
    let ?f = "\<lambda>x. if x = 0 then w^3 else 2*w^(x+3)"
    have "power_sum max_initial_coins = suminf ?f"
      using x_inner_sum by simp
    moreover have "suminf ?f = 1"
    proof -
      have "(\<lambda>x. ?f (x+1)) sums s \<Longrightarrow> ?f sums (s + (\<Sum>x<1. ?f x))" for s
        using sums_iff_shift by fastforce
      then have sum_split: "(\<lambda>x. ?f (x+1)) sums s \<Longrightarrow> ?f sums (s + ?f 0)" for s by simp

      have "(\<lambda>x. ?f (x+1)) sums (2*w^2)"
      proof -
        have "?f (x+1) = 2*w^(x+1+3)" for x by simp
        then have 1: "?f (x+1) = 2*w^(4+x)" for x by auto
        have 2: "(\<lambda>x. w^x) sums s \<Longrightarrow> (\<lambda>x. 2*w^(4+x)) sums (2*w^4*s)" for s
          using geometric_sum_transformation by simp

        from 2 w_geometric_sum have "(\<lambda>x. 2*w^(4+x)) sums (2*w^4/(w^2))" by fastforce
        then have 3: "(\<lambda>x. 2*w^(4+x)) sums (2*w^2)"
          by (smt (verit, ccfv_threshold) One_nat_def add.commute add_diff_cancel_right'
             comm_semiring_class.distrib divide_eq_0_iff le_add2 nat_1_add_1 numeral_3_eq_3
             numeral_plus_one plus_1_eq_Suc power_add power_diff real_sqrt_eq_1_iff semiring_norm(2)
             semiring_norm(8) times_divide_eq_right w_def)
        from 1 3 show ?thesis by simp
      qed
      then have f_sums: "?f sums (2*w^2 + w^3)" using sum_split by simp

      have "2*w^2 + w^3 = 2*w*w + w*w^2" by (smt (verit) One_nat_def nat_1_add_1 numeral_3_eq_3 
            plus_1_eq_Suc power.simps(2) power2_diff zero_power2)
      then have "2*w^2 + w^3 = w*(2*w + w^2)" by (simp add: ring_class.ring_distribs(1))
      then have "2*w^2 + w^3 = w*(2*w + 1 - w)" using w_squared by simp
      then have "2*w^2 + w^3 = w*(1 + w)" by simp
      then have "2*w^2 + w^3 = w + w^2" by (simp add: power2_eq_square ring_class.ring_distribs(1))
      then have "2*w^2 + w^3 = w + 1 - w" using w_squared by simp
      then have two_w2_plus_w3: "2*w^2 + w^3 = 1" by simp     

      from two_w2_plus_w3 f_sums show ?thesis using sums_unique by force
    qed
    ultimately show ?thesis by simp
  qed
qed

lemma max_initial_coins_infinite: "infinite max_initial_coins"
proof (rule ccontr)
  let ?proj = "((\<lambda>(x, _). x) ` max_initial_coins)"
  assume "\<not>infinite max_initial_coins"
  then have "finite max_initial_coins" by simp
  then have "finite ?proj" by auto
  moreover have "?proj \<noteq> {}" (* interesting shortcut sledgehammer took here: *)
    using finite_power_sum max_initial_coins_eq_one by force
  ultimately obtain k where max_k: "k \<in> ?proj \<and> (\<forall>j \<in> ?proj. k \<le> j \<longrightarrow> k = j)"
    using finite_has_maximal by metis

  have "(k+1, 5) \<in> max_initial_coins" using max_initial_coins_def by auto
  then have "k+1 \<in> ?proj" by auto
  then show "False" using max_k by auto
qed

theorem initial_finite_coins_less_one:
  assumes initial: "initial_coins coins"
      and finite:"finite coins"
shows "power_sum coins < 1"
proof -
  have "coins \<subseteq> max_initial_coins" by (simp add: initial initial_coins_subset)
  moreover have "coins \<noteq> max_initial_coins" using finite max_initial_coins_infinite by blast
  ultimately have "coins \<subset> max_initial_coins" by blast
  then have "power_sum coins < power_sum max_initial_coins" using powersum_subset_less by auto
  then show ?thesis using max_initial_coins_eq_one by simp
qed

(* Not sure if this lemma is needed, but it is easy enough to prove. TODO *)
theorem initial_coins_leq_one:
  assumes "initial_coins coins"
  shows "power_sum coins \<le> 1"
  by (metis assms initial_coins_subset max_initial_coins_eq_one powersum_subset_leq)





theorem jump_decreases_power_sum: "jump A B \<Longrightarrow> power_sum B \<le> power_sum A"
proof (induction rule: jump.induct)
  case (left x y A B)
  let ?x = "nat (abs x)"
  let ?full_diff = "w^(y + nat (abs (x-2))) - w^(y + nat (abs (x-1))) - w^(y + nat (abs x))"
  have power_sum_B: "power_sum (A - {(x, y), (x - 1, y)} \<union> {(x - 2, y)})
      = power_sum A + ?full_diff"
    using \<open>(x, y) \<in> A\<close> \<open>(x-1, y) \<in> A\<close> \<open>(x-2, y) \<notin> A\<close> power_sum_minus_singleton power_sum_union_singleton
    by (smt (verit, del_insts) Diff_iff Diff_insert2 add.commute insertE insert_Diff prod.inject)

  then have "?full_diff = w^y*w^(nat (abs (x-2))) - w^y*w^(nat (abs (x-1))) - w^y*w^(nat (abs x))" by (metis power_add)
  then have full_diff_diff: "?full_diff = w^y * (w^(nat (abs (x-2))) - w^(nat (abs (x-1))) - w^(nat (abs x)))" 
    (is "?full_diff = w^y * ?diff") by (simp add: right_diff_distrib)

  have "?diff  \<le> 0"
  proof (cases "x \<le> 0")
    case x_nonpos: True
    then have "?diff = w^(?x+2) - w^(?x+1) - w^(?x)"
      by (smt (verit, ccfv_threshold) nat_1_add_1 nat_add_distrib nat_numeral numeral_eq_one_iff)
    then show ?thesis
      by (smt (verit, del_insts) w_range w_recurrence zero_less_power)
  next
    case x_pos: False
    then show ?thesis proof (cases "x \<ge> 2")
      case x_geq_2: True
      have "?diff = w^(?x-2) - w^(?x-1) - w^(?x)" proof -
        have "nat (abs (x-2)) = ?x - 2" using x_geq_2 by (simp add: nat_diff_distrib')
        moreover have "nat (abs (x-1)) = ?x - 1" using x_geq_2 by (simp add: nat_diff_distrib')
        ultimately show ?thesis by presburger
      qed
      then have "?diff = w^(?x-2) - w^(?x-2+1) - w^(?x-2+2)"
        by (smt (verit, del_insts) Nat.add_diff_assoc2 Nat.diff_diff_right One_nat_def cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq' diff_zero le_add2 linorder_linear nat_0_iff nat_1_add_1 nat_2 nat_diff_distrib plus_1_eq_Suc x_geq_2)
      then show ?thesis by (smt (verit, ccfv_SIG) w_recurrence)
    next
      case x_eq_1_or_2: False
      then show ?thesis proof (cases "x = 1")
        case x_eq_1: True
        then show ?thesis by auto
      next
        case x_eq_2: False
        then show ?thesis using x_eq_1_or_2 x_pos by fastforce
      qed
    qed
  qed
  moreover have "w^y > 0" by (simp add: w_range)
  ultimately have "?full_diff \<le> 0" using full_diff_diff zero_less_mult_iff by smt
  then show ?case using left.hyps(4) by (smt (verit, best) power_sum_B)
next
  (* 
    Luckily, the "right" part is more or less the "left" part with signs changed
  *)
  case (right x y A B)
  let ?x = "nat (abs x)"
  let ?full_diff = "w^(y + nat (abs (x+2))) - w^(y + nat (abs (x+1))) - w^(y + nat (abs x))"
  have power_sum_B: "power_sum (A - {(x, y), (x + 1, y)} \<union> {(x + 2, y)})
      = power_sum A + ?full_diff"
    using \<open>(x, y) \<in> A\<close> \<open>(x+1, y) \<in> A\<close> \<open>(x+2, y) \<notin> A\<close> power_sum_minus_singleton power_sum_union_singleton
    by (smt (z3) Diff_iff Diff_insert2 add.commute insertE insert_Diff prod.inject)

  then have "?full_diff = w^y*w^(nat (abs (x+2))) - w^y*w^(nat (abs (x+1))) - w^y*w^(nat (abs x))" by (metis power_add)
  then have full_diff_diff: "?full_diff = w^y * (w^(nat (abs (x+2))) - w^(nat (abs (x+1))) - w^(nat (abs x)))" 
    (is "?full_diff = w^y * ?diff") by (simp add: right_diff_distrib)

  have "?diff  \<le> 0"
  proof (cases "x \<ge> 0")
    case x_nonneg: True
    then have "?diff = w^(?x+2) - w^(?x+1) - w^(?x)"
      by (smt (verit, ccfv_threshold) nat_1_add_1 nat_add_distrib nat_numeral numeral_eq_one_iff)
    then show ?thesis
      by (smt (verit, del_insts) w_range w_recurrence zero_less_power)
  next
    case x_neg: False
    then show ?thesis proof (cases "x \<le> -2")
      case x_leq_minus2: True
      have "?diff = w^(?x-2) - w^(?x-1) - w^(?x)" proof -
        have "nat (abs (x+2)) = ?x - 2" using x_leq_minus2 by (simp add: nat_diff_distrib')
        moreover have "nat (abs (x+1)) = ?x - 1" using x_leq_minus2 by (simp add: nat_diff_distrib')
        ultimately show ?thesis by presburger
      qed
      then have "?diff = w^(?x-2) - w^(?x-2+1) - w^(?x-2+2)"
        by (smt (verit, del_insts) Nat.add_diff_assoc2 Nat.diff_diff_right One_nat_def cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq' diff_zero le_add2 linorder_linear nat_0_iff nat_1_add_1 nat_2 nat_diff_distrib plus_1_eq_Suc x_leq_minus2)
      then show ?thesis by (smt (verit, ccfv_SIG) w_recurrence)
    next
      case x_eq_minus_1_or_minus_2: False
      then show ?thesis proof (cases "x = -1")
        case x_eq_minus_1: True
        then show ?thesis by auto
      next
        case x_eq_minus_2: False
        then show ?thesis using x_eq_minus_1_or_minus_2 x_neg by fastforce
      qed
    qed
  qed
  moreover have "w^y > 0" by (simp add: w_range)
  ultimately have "?full_diff \<le> 0" using full_diff_diff zero_less_mult_iff by smt
  then show ?case using right.hyps(4) by (smt (verit, best) power_sum_B)
next
  case (up x y A B)
  let ?x = "nat (abs x)"

  let ?full_diff = "w^(?x + (y-2)) - w^(?x + (y-1)) - w^(?x + y)"
  have power_sum_B: "power_sum (A - {(x, y), (x, y-1)} \<union> {(x, y-2)})
      = power_sum A + ?full_diff"
    using \<open>(x, y) \<in> A\<close> \<open>(x, y-1) \<in> A\<close> \<open>(x, y-2) \<notin> A\<close> power_sum_minus_singleton power_sum_union_singleton
    by (smt (verit) Diff_insert2 diff_diff_left insert_Diff insert_iff nat_1_add_1 prod.inject)

  then have "?full_diff = w^(?x)*w^(y-2) - w^(?x)*w^(y-1) - w^(?x)*w^y" by (metis power_add)
  then have full_diff_diff: "?full_diff = w^(?x) * (w^(y-2) - w^(y-1) - w^y)" 
    (is "?full_diff = w^(?x) * ?diff") by (simp add: right_diff_distrib)

  have "?diff  \<le> 0"
  proof (cases "y \<ge> 2")
    case True
    then have "?diff = w^(y-2) - w^(y-2+1) - w^(y-2+2)" using nat_le_iff_add by auto
    then have "?diff = 0" using w_recurrence[where n="y-2"] by simp
    then show ?thesis by simp
  next
    case False
    then show ?thesis using \<open>(x, y - 1) \<in> A\<close> \<open>(x, y - 2) \<notin> A\<close> by auto
  qed
  moreover have "w^?x > 0" by (simp add: w_range)
  ultimately have "?full_diff \<le> 0" using full_diff_diff zero_less_mult_iff by smt
  then show ?case using up.hyps(4) by (smt (verit, best) power_sum_B)
next
  case (down x y A B)
  let ?x = "nat (abs x)"

  let ?full_diff = "w^(?x + (y+2)) - w^(?x + (y+1)) - w^(?x + y)"
  have power_sum_B: "power_sum (A - {(x, y), (x, y+1)} \<union> {(x, y+2)})
      = power_sum A + ?full_diff"
    using \<open>(x, y) \<in> A\<close> \<open>(x, y+1) \<in> A\<close> \<open>(x, y+2) \<notin> A\<close> power_sum_minus_singleton power_sum_union_singleton
    by (smt (verit) Diff_iff Diff_insert2 add_diff_cancel_left' diff_is_0_eq' insertE insert_Diff nle_le one_neq_zero prod.inject)

  then have "?full_diff = w^(?x)*w^(y+2) - w^(?x)*w^(y+1) - w^(?x)*w^y" by (metis power_add)
  then have full_diff_diff: "?full_diff = w^(?x) * (w^(y+2) - w^(y+1) - w^y)" 
    (is "?full_diff = w^(?x) * ?diff") by (simp add: right_diff_distrib)

  have "?diff  \<le> 0" by (smt (verit) w_range w_recurrence zero_less_power)
  moreover have "w^?x > 0" by (simp add: w_range)
  ultimately have "?full_diff \<le> 0" using full_diff_diff zero_less_mult_iff by smt
  then show ?case using down.hyps(4) by (smt (verit, best) power_sum_B)
qed

end