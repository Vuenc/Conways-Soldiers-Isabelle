(*  Title       : LeapingFrog.thy
    Author      : Vincent Bürgin

    This theory formalizes Conway's Soldiers, also known as the Leaping Frog game.

    The game is played on the infinite grid (Z x N), where the top row corresponds to an y
      coordinate of 0. An arbitrary amount of coins can be placed on the grid below the line y = 5,
      i.e. starting at the sixth row.
    Then the coins can be moved according to peg solitaire rules:
      A coin may jump over an adjacent coin vertically or horizontally. The coin it jumped over
      is removed from the board.
    The objective is to reach the top row (y = 0) with a coin. John Conway proved that this is not
      possible, using an argument involving the golden ratio phi: Let w = 1/phi = phi - 1.
      Assign the field (x, y) the power w^(x+y). Then the sum of all fields occupied by an initial
      coin configuration is at most 1, however the value of the goal field (0, 0) is 1 as well.
      Furthermore, performing moves cannot increase the sum of occupied fields.
      From this, it is shown that the goal field cannot be reached in a finite number of moves.

          ................... <-- Goal row.
          ...................
          ...................
          ...................
          ...................
          ooooooooooooooooooo <-- On this row and below, coins may be placed.
          ooooooooooooooooooo
          ooooooooooooooooooo     The grid extends infinitely to the left, right and bottom.

    References:
    - E. Berlekamp, J. Conway and R. Guy, Winning Ways for Your Mathematical Plays
    - Claudi Alsina and Roger B. Nelsen, Charming Proofs: A Journey Into Elegant Mathematics
    - Miguel de Guzmán, https://www.oma.org.ar/red/la_rana.htm (online explanation of the proof
        as performed here, in Spanish)
*)

theory LeapingFrog
  imports Main HOL.Real HOL.NthRoot HOL.Boolean_Algebras HOL.Series "HOL-IMP.Star"
begin

section \<open>The number w\<close>

(*
  Definition of the number w = (golden ratio) - 1
*)
definition w :: "real" where
"w = (sqrt 5 - 1)/2"

(*
  Recurrence relations the powers of w satisfy:
    -   w^2 = 1 - w
    -   w^(n+1) + w^(n+2) = w^n

  These relations will be crucial for the whole argument to work.
*)
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

lemma w_recurrence: "w^(n+1) + w^(n+2) = w^n"
proof -
  have "w^(n+1) + w^(n+2) = w^n*(w + w^2)"
    by (smt (verit) power_add power_one_right right_diff_distrib)
  moreover have "w + w^2 = 1" using w_squared by simp
  ultimately show ?thesis by simp
qed

(*
  w is in (0, 1): We will need this to prove the limit of the geometric series with base w.
*)
lemma w_range: "w > 0 \<and> w < 1"
proof -
  have "sqrt 5 > 1" by force
  then have 1: "w > 0" by (simp add: w_def)
  have "w^2 < 1" using w_def w_squared using 1 by linarith
  then have 2: "w < 1" by (smt (verit) one_le_power)
  then show ?thesis using 1 2 by blast
qed

(*
  We will use this to have an upper bound for 1/(1-w).
*)
lemma w_bound:"1 - w > 1/4"
proof -
  have "sqrt 5 - 1 > 1" by (smt (verit, ccfv_SIG) real_sqrt_four real_sqrt_less_iff)
  then have "w > 1/2" using w_def by force
  then have "w^2 > 1/4" by (simp add: power_divide w_def)
  then show ?thesis by (simp add: w_squared)
qed

section \<open>Leaping Frog game definitions\<close>

(*
  The game is played on a grid in the half-plane: grid cells have `int` x coordinates and `nat`
    y coordinates. A coin configuration `coins` is a set of grid cell positions.
*)
type_synonym position = "(int \<times> nat)"
type_synonym coins = "position set"

subsection \<open>Jumping predicates\<close>
(*
  A coin configuration A can transitions to a coin configuration B as follows:  A coin in A can jump
    over an (horizontally or vertically) adjacent coin if the next cell behind is unoccupied.
    The coin that it jumped over is removed. The resulting configuration is B, and A and B are
    related via `jump`.

  Example: |o|o|.|  \<longrightarrow>  |.|.|o| (left coin jumps over the middle coin).
*)
inductive jump :: "coins \<Rightarrow> coins \<Rightarrow> bool" where
  left: "\<lbrakk>(x,y) \<in> A; (x-1, y) \<in> A; (x-2, y) \<notin> A; B = (A - {(x,y), (x-1,y)}) \<union> {(x-2, y)}\<rbrakk>
    \<Longrightarrow> jump A B"
| right: "\<lbrakk>(x,y) \<in> A; (x+1, y) \<in> A; (x+2, y) \<notin> A; B = (A - {(x,y), (x+1,y)}) \<union> {(x+2, y)}\<rbrakk>
    \<Longrightarrow> jump A B"
| up: "\<lbrakk>(x,y) \<in> A; (x, y-1) \<in> A; (x, y-2) \<notin> A; B = (A - {(x,y), (x,y-1)}) \<union> {(x, y-2)}\<rbrakk>
    \<Longrightarrow> jump A B"
| down: "\<lbrakk>(x,y) \<in> A; (x, y+1) \<in> A; (x, y+2) \<notin> A; B = (A - {(x,y), (x,y+1)}) \<union> {(x, y+2)}\<rbrakk>
    \<Longrightarrow> jump A B"

(*
  A and B are related via `jumps` if B can be reached from A via a chain of multiple `jump`s.
*)
definition jumps :: "coins \<Rightarrow> coins \<Rightarrow> bool"  where
"jumps = star jump"

(*
  Some examples of the `jump` and `jumps` predicates
*)
lemma example_right: "jump {(0, 0), (1, 0)} {(2, 0)}"
  by (rule jump.right[of 0 0]) auto
lemma example_left: "jump {(0, 0), (-1, 0)} {(-2, 0)}"
  by (rule jump.left[of 0 0]) auto
lemma example_up: "jump {(0, 2), (0, 1)} {(0, 0)}"
  by (rule jump.up[of 0 2]) auto
lemma example_down: "jump {(0, 0), (0, 1)} {(0, 2)}"
  by (rule jump.down[of 0 0]) auto
lemma example_two_jumps: "jumps {(0,0), (0,1), (1,2)} {(2,2)}"
unfolding jumps_def proof (rule star.step)
  show "jump {(0,0), (0,1), (1,2)} {(0,2), (1,2)}"
    by (rule jump.down[of 0 0]) auto
  have "jump {(0,2), (1,2)} {(2,2)}"
    by (rule jump.right[of 0 2]) auto 
  then show "star jump {(0, 2), (1, 2)} {(2, 2)}" by blast
qed

subsection \<open>Coin grid and initial configurations\<close>
(*
  Definitions and facts about initial configurations:

  In the beginning of the game, coins may be placed below the line "y = 5". Coin configurations
    where all coins are below this line are initial configurations. Any initial configuration is a
    subset of the maximal initial configuration, where all coins below the line are present.
*)
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

subsection \<open>Assigning powers of w to grid cells/Sums of powers of w to coin configurations\<close>

(*
  In the original proof, every grid cell is assigned the power w^(|x|+y).

  We want to avoid series over `int` since `Series.thy` uses series over `nat`. We therefore assign
    powers as follows:
  - The coordinate (0::nat, y::nat) is assigned w^y
  - The coordinate (x::nat, y::nat), x > 0, is assigned 2*w^(x+y) and captures the sum of the powers
      assigned to the grid cells (-x::int, y) and (x::int, y)

  `point_pow` defines this assignment for all positions (x, y) contained in a coin configuration.
*)
fun point_pow :: "coins \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
"point_pow c x y = (if (int(x), y) \<in> c then w^(x+y) else 0)
  + (if (-int(x), y) \<in> c \<and> x > 0 then w^(x+y) else 0)"

(*
  `power_sum` sums up the values of w^(x+y) for all coin positions in a coin configuration via
    a double series.
*)
fun power_sum :: "coins \<Rightarrow> real" where
"power_sum c = suminf (\<lambda>x. suminf (point_pow c x))"

section \<open>Properties of power sums of w\<close>
text \<open>This section contains proofs about the `power_sum` function:
  - The inner series and the outer series that define `power_sum` converge,
  - the value of `power_sum` for finite coin configurations can be computed via `sum`,
  - considering a (proper) subset of coins (strictly) decreases the power sum\<close>

subsection \<open>Preliminary lemmas\<close>

(* 
  Kind of specific lemma about transforming geometric series, but an argument of this form
   is needed quite often in the following and is a bit of work to prove.
*)
lemma geometric_sums_transformation: "norm (b::real) < 1 \<Longrightarrow> (\<lambda>y. c*b^(a+y)) sums (c*b^(a)/(1-b))"
proof -
  let ?s = "1/(1-b)"
  assume "norm b < 1"
  then have "(\<lambda>y. b^y) sums ?s" using geometric_sums by blast
  (* Convert the series to a limit so we can apply multiplication lemmas about limits *)
  then have sum_unfold: "(\<lambda>n. \<Sum>i<n. (\<lambda>y. b^y) i) \<longlonglongrightarrow> ?s" by (simp add: sums_def)
  have "(\<lambda>_. c*w^a) \<longlonglongrightarrow> c*w^a" by simp
  from this sum_unfold have 
    "(\<lambda>n. c*b^a * (\<Sum>i<n. (\<lambda>y. b^y) i)) \<longlonglongrightarrow> c*b^a * ?s"
    using tendsto_mult by blast
  moreover have "c*b^a * (\<Sum>i<(n::nat). (\<lambda>y. b^y) i) 
      = (\<Sum>i<n. (\<lambda>y. c*b^a * b^y) i)" for n
    using sum_distrib_left by blast
  moreover have "(\<Sum>i<n. (\<lambda>y. c*b^a * b^y) i) = (\<Sum>i<n. (\<lambda>y. c*b^(a+y)) i)"
    for n by (metis ab_semigroup_mult_class.mult_ac(1) power_add)
  ultimately have "(\<lambda>n. (\<Sum>i<n. (\<lambda>y. c*b^(a+y)) i)) \<longlonglongrightarrow> c*b^a * ?s" by simp
  then have "(\<lambda>y. c*b^(a+y)) sums (c*b^a * ?s)" by (simp add: sums_def)
  then show ?thesis by simp
qed

(*
  The geometric sum transformation lemma holds for b=w, because w is in (0, 1).
*)
corollary geometric_w_sums_transformation: "(\<lambda>y. c*w^(a+y)) sums (c*w^(a)/(1-w))"
  using w_range geometric_sums_transformation[where b=w] by simp

(*
  Variant of the comparison test: if a sequence f is summable and dominates another non-negative
    sequence g, then g is summable as well.
*)
lemma summable_nonneg_comparison_test:
  assumes f_summable: "summable (f::nat \<Rightarrow> real)"
      and f_dom_g: "\<And>i. g i \<le> f i"
      and nonneg: "\<And>i. 0 \<le> g i"
shows "summable g"
proof -
  have "\<forall>n. norm (g n) \<le> f n" by (simp add: f_dom_g nonneg)
  then show ?thesis using summable_comparison_test f_summable by blast
qed

(*
  Changing one term of a summable series by d changes the sum by d.
*)
lemma series_one_term_different:
  assumes f_g_diff: "(g :: nat \<Rightarrow> real) (k::nat) = f k + d"
      and f_g_eq: "\<And>i. i \<noteq> k \<Longrightarrow> f i = g i"
      and "summable f"
    shows "suminf g = suminf f + d"
proof -
  (* Decompose series into initial part until the different element, and equal tail part *)
  have f_initsum:  "(\<lambda>i. f (i + (k+1))) sums s \<longleftrightarrow> f sums (s + (\<Sum>i<k+1. f i))" 
    for s using sums_iff_shift by blast
  have g_initsum:  "(\<lambda>i. g (i + (k+1))) sums s \<longleftrightarrow> g sums (s + (\<Sum>i<k+1. g i))" 
    for s using sums_iff_shift by blast
  (* The the initial parts differ by d... *)
  have init_diff: "(\<Sum>i<k+1. g i) = (\<Sum>i<k+1. f i) + d"
  proof -
    have "(\<Sum>i<k+1. g i) = (\<Sum>i<k. g i) + g k" by simp
    moreover have "(\<Sum>i<k+1. f i) = (\<Sum>i<k. f i) + f k" by simp
    moreover have "(\<Sum>i<k. g i) = (\<Sum>i<k. f i)" using f_g_eq by simp
    ultimately show ?thesis using f_g_diff by simp
  qed
  (* ...and the tails are equal *)
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

subsection \<open>Summability of inner/outer series defining `power_sum`\<close>

(*
  Value of inner series for x = 0, given that all coins are present.
*)
lemma point_pow_all_coins_row_sum_x_eq_0:
  "x = 0 \<Longrightarrow> (point_pow all_coins x) sums (1/(1-w))"
proof -
  assume "x = 0"
  (* Since x = 0, point_pow only counts the x = 0 column *)
  then have "point_pow all_coins x y = w^y" for y by (simp add: all_coins_def)
  moreover have "(\<lambda>y. w^y) sums (1/(1-w))" using geometric_sums w_range by force
  ultimately show ?thesis using sums_cong by blast
qed

(*
  Value of inner series for x > 0, given that all coins are present.
*)
lemma point_pow_all_coins_row_sum_x_ge_0:
  "x > 0 \<Longrightarrow> (point_pow all_coins x) sums (2*w^x/(1-w))"
proof -
  assume "x > 0"
  (* Since x > 0, point_pow only counts the x and the -x columns (hence the factor of 2) *)
  then have "point_pow all_coins x y = 2 * w^(x+y)" for y by (simp add: all_coins_def)
  moreover have "(\<lambda>y. 2 * w^(x+y)) sums (2*w^x/(1-w))" 
    using geometric_w_sums_transformation by fastforce
  ultimately show ?thesis by presburger
qed

(*
  The inner series converges if all coins are present.
*)
lemma point_pow_all_coins_row_summable: "summable (point_pow all_coins x)"
proof (cases "x = 0")
  case True 
  then show ?thesis using point_pow_all_coins_row_sum_x_eq_0 using summable_def by blast
next
  case False
  then show ?thesis using point_pow_all_coins_row_sum_x_ge_0 using summable_def by blast
qed

(*
  The inner series converges for any coin configuration.
*)
lemma point_pow_summable: "summable (point_pow coins x)" 
proof -
  have "summable (point_pow all_coins x)" by (rule point_pow_all_coins_row_summable)
  (* Use that point_pow for all coins dominates point_pow for a subset of coins *)
  moreover have "point_pow coins x y \<le> point_pow all_coins x y" for y
    using all_coins_def w_range by auto
  ultimately show ?thesis using summable_nonneg_comparison_test w_range by fastforce
qed

(*
  The outer series converges for any coin configuration.
*)
lemma power_sum_summable: "summable (\<lambda>x. suminf (point_pow coins x))"
proof -
  let ?f = "\<lambda>x. suminf (point_pow all_coins x)"
  (* Both the x = 0 and x > 0 case can be upper-bounded by 2*1/(1-w).
     For convenience, we upper-bound the factor 2*1/(1-w) by 8 *)
  have "1/(1-w) < 4" using w_bound w_range by (simp add: mult_imp_div_pos_less)
  then have "1/(1-w) \<le> 4" by simp
  have "?f x \<le> 8 * w^x" for x proof (cases "x = 0")
    case xeq0: True
    then have "?f x = 1/(1-w)" using point_pow_all_coins_row_sum_x_eq_0 sums_unique by force
    moreover have "1/(1-w) \<le> 2/(1-w) * w^0"
      by (metis diff_ge_0_iff_ge divide_right_mono less_le mult.commute mult_cancel_right2 
          one_le_numeral power_0 w_range)
    ultimately show ?thesis using xeq0 \<open>1/(1-w) < 4\<close> by fastforce
  next
    case False
    then have "?f x = 2*w^x/(1-w)"
      by (metis bot_nat_0.not_eq_extremum point_pow_all_coins_row_sum_x_ge_0 sums_unique)
    moreover have "1/(1-w) * w^x < 4 * w^x" using \<open>1/(1-w) < 4\<close> w_range
      by (meson mult_less_cancel_right_disj zero_less_power)
    ultimately show ?thesis by force
  qed
  (* This upper bound is now easily shown to be summable. *)
  moreover have "(\<lambda>x. 8*w^x) sums (8/(1-w))"
    using geometric_w_sums_transformation[where a=0] by simp
  then have "summable (\<lambda>x. 8*w^x)" using sums_summable by blast
  moreover have "0 \<le> suminf (point_pow all_coins x)" for x
    using point_pow_summable suminf_nonneg w_range by force
  (* The original series (with all coins) is dominated by the upper bound, i.e. also summable. *)
  ultimately have "summable ?f" using summable_nonneg_comparison_test by presburger

  (* Furthermore, the series with all coins dominates the one with just a subset of coins, ...*)
  have "point_pow coins x y \<le> point_pow all_coins x y" for x y using all_coins_def w_range by auto
  then have "suminf (point_pow coins x) \<le> suminf (point_pow all_coins x)" for x 
    by (meson point_pow_summable suminf_le)
  moreover have "0 \<le> suminf (point_pow coins x)" for x
    using point_pow_summable suminf_nonneg w_range by force

  (* ...therefore this is summable as well. *)
  ultimately show ?thesis
    using \<open>summable ?f\<close> summable_nonneg_comparison_test by presburger
qed


subsection \<open>Computing `power_sum` for finite coin configurations\<close>

(*
  Adding a single coin (x, y) to a coin configuration increases its `power_sum` by w^(|x| + y)
*)
lemma power_sum_union_singleton:
  "(x,y) \<notin> F \<Longrightarrow> power_sum (F \<union> {(x,y)}) = power_sum F + w^(nat (abs x) + y)"
proof -
  assume notinF: "(x,y) \<notin> F"
  let ?Fnew = "insert (x,y) F"
  (* ?x is the `nat` absolute value of x that is used as index in the series *)
  let ?x = "nat (abs x)"

  (* 
    We have some fixed coin (x, y) and show that the double series that defines `power_sum`
      differs by w^(?x + y).
  
    Proceed in four steps:
    - for all x' \<noteq> ?x, the value of the inner series remains equal
    - for all y' \<noteq> y and all x', the value of point_pow remains equal
    - for ?x and y, the value of point_pow differs by w^(?x + y)
    - for ?x, the value of the inner series differs by w^(?x + y)

    Then, the outer series only differs by the single term for ?x, and `series_one_term_different`
      can be applied.
  *)

  have otherx: "x' \<noteq> ?x \<Longrightarrow> suminf (point_pow ?Fnew x') = suminf (point_pow F x')" for x'
  proof -
    assume xneq: "x' \<noteq> ?x"
    from xneq have poseq: "(x', y) \<in> F \<longleftrightarrow> (x', y) \<in> ?Fnew" by fastforce
    from xneq have negeq: "(-x', y) \<in> F \<longleftrightarrow> (-x', y) \<in> ?Fnew" by fastforce
    from poseq negeq show ?thesis by (smt (verit, ccfv_threshold) Pair_inject case_prod_conv
          insert_iff point_pow.elims suminf_cong notinF)
  qed

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
      then show ?thesis by (smt (verit, del_insts) notinF insert_iff 
            int_nat_eq point_pow.elims prod.inject zero_less_nat_eq)
    qed
  qed

  have samex: "suminf (point_pow ?Fnew ?x) = suminf (point_pow F ?x) + w^(?x+y)"
    using series_one_term_different samexy othery point_pow_summable by presburger

  have "suminf (\<lambda>x. suminf (point_pow ?Fnew x)) = suminf (\<lambda>x. suminf (point_pow F x)) + w^(?x+y)"
    using series_one_term_different samex otherx power_sum_summable by presburger
  then show ?thesis by simp
qed

(*
  Removing a single coin (x, y) from a coin configuration decreases its `power_sum` by w^(|x| + y)
*)
corollary power_sum_minus_singleton:
  "(x,y) \<in> F \<Longrightarrow> power_sum (F - {(x,y)}) = power_sum F - w^(nat (abs x) + y)"
  using mk_disjoint_insert power_sum_union_singleton by fastforce

(*
  For a finite coin configuration, we can compute the `power_sum` using the `sum` function.
*)
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

subsection \<open>Monotonicity of `power_sum` in the coin configuration\<close>

(*
  Lemmas showing that `power_sum` weakly increases with a  \<subseteq>-increasing coin configuration.
*)
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

(*
  Lemmas showing that `power_sum` strictly increases with a \<subset>-increasing coin configuration.
*)
lemma point_pow_subset_less: "A \<subseteq> B \<and> (x,y) \<in> B - A 
    \<Longrightarrow> point_pow A (nat (abs x)) y < point_pow B (nat (abs x)) y"
  by (smt (verit, best) DiffD2 Diff_partition Un_iff nat_eq_iff point_pow.elims w_range
        zero_less_nat_eq zero_less_power)

lemma powersum_subset_less:
  "A \<subset> B \<Longrightarrow> power_sum A < power_sum B"
proof -
  assume subset: "A \<subset> B"
  then obtain x y where xy: "(x,y) \<in> B - A" by auto
  let ?x = "nat (abs x)"

  (*
    Proof strategy: Show that the differences of the series is > 0. We start from the innermost
      terms in the series and work our way outward. Along the way we need the `suminf_diff` lemma
      and some summability statements.
  *)

  (* Show that the series of differences of inner series terms for ?x sums to something > 0  *)
  have "point_pow B ?x y - point_pow A ?x y > 0" using xy point_pow_subset_less
    by (simp add: order_less_imp_le subset)
  moreover have "summable (\<lambda>y. point_pow B ?x y - point_pow A ?x y)"
    using point_pow_summable summable_diff by blast
  ultimately have "suminf (\<lambda>y. point_pow B ?x y - point_pow A ?x y) > 0"
    by (smt (verit) order_less_imp_le point_pow_subset_leq subset suminf_pos_iff)

  (* Pull this apart to show that the difference of the inner series for ?x is > 0 *)
  moreover have "suminf (\<lambda>y. point_pow B ?x y - point_pow A ?x y)
    = suminf (point_pow B ?x) - suminf (point_pow A ?x)" 
    using suminf_diff[of "point_pow B ?x" "point_pow A ?x"] point_pow_summable by simp
  ultimately have "suminf (point_pow B ?x) - suminf (point_pow A ?x) > 0" by simp

  (* Using that the inner series difference for other x is \<ge> 0 ...*) 
  moreover have "suminf (point_pow B x) - suminf (point_pow A x) \<ge> 0" for x
    by (simp add: order_less_imp_le powersum_inner_subset_leq subset)
  moreover have "summable (\<lambda>x. suminf (point_pow B x) - suminf (point_pow A x))"
    by (simp add: power_sum_summable summable_diff)
  (* ...show that the series of differences of outer series terms is > 0 *)
  ultimately have "suminf (\<lambda>x. suminf (point_pow B x) - suminf (point_pow A x)) > 0" 
    using suminf_pos_iff[where f="(\<lambda>x. suminf (point_pow B x) - suminf (point_pow A x))"] by blast

  (* Pull this apart to get that the difference of the outer series is > 0 *)
  then have "suminf (\<lambda>x. suminf (point_pow B x)) - suminf (\<lambda>x. suminf (point_pow A x)) > 0" 
    using suminf_diff[of "(\<lambda>x. suminf (point_pow B x))" "(\<lambda>x. suminf (point_pow A x))"]
          power_sum_summable by presburger
  then show ?thesis by simp
qed


section \<open>Power sums for game configurations\<close>

text \<open>This section shows some facts about `power_sum`s of coin configurations relevant to the game:
  - the goal field has a `power_sum` value of 1,
  - the maximal initial configuration has a `power_sum` value of 1,
  - initial configurations have a `power_sum` value of at most 1.\<close>

subsection \<open>Power sum of goal field\<close>

(*
  The set containing only the goal field {(0,0)} has a `power_sum` value of 1
*)
corollary goal_field_value_1: "power_sum {(0,0)} = 1"
  using finite_power_sum by simp


subsection \<open>Power sums of initial coin configurations\<close>

(*
  The `power_sum` of the maximal initial coin configuration is 1.
  (This is the first crucial property of the number w.)
*)
theorem max_initial_coins_eq_one: "power_sum max_initial_coins = 1"
proof -
  (* Compute the inner series for the x = 0 column *)
  have x_eq_0: "x = 0 \<Longrightarrow> suminf (point_pow max_initial_coins x) = w^3" for x
  proof -
    assume "x = 0"
    have point_pow_unfold: "point_pow max_initial_coins x y = (if y \<ge> 5 then w^y else 0)" for y
      by (simp add: \<open>x = 0\<close> max_initial_coins_def)
    let ?f = "(\<lambda>y. (if y \<ge> 5 then w^y else 0))"

    (* Drop the initial (zero) segment of the series, by shifting the index by 5 *)
    have 1: "(\<lambda>y. w^(y+5)) sums s \<Longrightarrow> ?f sums s" for s
    proof -
      assume "(\<lambda>y. w^(y+5)) sums s"
      then have "(\<lambda>y. ?f (y + 5)) sums s" using le_add2 by presburger
      then have "?f sums (s + (\<Sum>i<5. ?f i))" using sums_iff_shift by blast
      then have "?f sums s" by simp
      then show ?thesis by simp
    qed

    (* Compute the geometric sum and do some work to show w^5/(1-w) = w^3 *)
    have "(\<lambda>y. w^(5+y)) sums (w^5/(1-w))" using geometric_w_sums_transformation[where c=1] by simp
    then have "(\<lambda>y. w^(5+y)) sums (w^5/w^2)" using w_squared by auto
    moreover have "(w^5/w^2) = w^(Suc(Suc(Suc(Suc(Suc 0)))))/w^(Suc(Suc 0))"
      by (simp add: numeral_2_eq_2 numeral_Bit1)
    then have "w^5/w^2 = w^3" by (simp add: numeral_3_eq_3)
    ultimately have "(\<lambda>y. w^(y+5)) sums w^3" by (metis (no_types, lifting) add.commute sums_cong)
    from this 1 have "?f sums w^3" by simp
    from this show ?thesis by (smt (verit, best) point_pow_unfold suminf_cong sums_unique)
  qed

  (* Compute the inner series for the x > 0 columns *)
  have x_ge_0: "x > 0 \<Longrightarrow> suminf (point_pow max_initial_coins x) = 2*w^(x+3)" for x
  proof -
    assume "x > 0"
    have point_pow_unfold: "point_pow max_initial_coins x y = (if y \<ge> 5 then 2*w^(x+y) else 0)" 
      for y by (simp add: \<open>x > 0\<close> max_initial_coins_def)
    let ?f = "(\<lambda>y. (if y \<ge> 5 then 2*w^(x+y) else 0))"

    (* Drop the initial (zero) segment of the series, by shifting the index by 5 *)
    have 1: "(\<lambda>y. 2*w^(x+y+5)) sums s \<Longrightarrow> ?f sums s" for s
    proof -
      assume "(\<lambda>y. 2*w^(x+y+5)) sums s"
      then have "(\<lambda>y. ?f (y + 5)) sums s" using le_add2
        by (smt (verit, ccfv_SIG) group_cancel.add1 sums_cong)
      then have "?f sums (s + (\<Sum>i<5. ?f i))" using sums_iff_shift by blast
      then have "?f sums s" by simp
      then show ?thesis by simp
    qed

    (* Compute the geometric sum and do some work to show 2*w^(x+5)/(1-w) = 2*w^(x+3) *)
    have "(\<lambda>y. 2*w^(x+5+y)) sums (2*w^(x+5)/(1-w))" using geometric_w_sums_transformation by simp
    then have 2: "(\<lambda>y. 2*w^(x+y+5)) sums (2*w^(x+5)/(1-w))"
      by (smt (verit) Groups.add_ac(2) group_cancel.add1 sums_cong)

    have "2 \<le> x+5" by simp
    then have "2*w^(x+5)/w^2 = 2*w^(x+5-2)" using power_diff
      by (smt (verit, ccfv_threshold) comm_semiring_class.distrib divide_eq_0_iff
          field_class.field_divide_inverse real_sqrt_eq_1_iff w_def)
    moreover have "x+5-2 = x+3" by simp
    ultimately have w_pow_diff: "2*w^(x+5)/w^2 = 2*w^(x+3)" by simp


    from 2 have "(\<lambda>y. 2*w^(x+y+5)) sums (2*w^(x+5)/w^2)" using w_squared by auto
    from this w_pow_diff have "(\<lambda>y. 2*w^(x+y+5)) sums (2*w^(x+3))" by metis
    from this 1 have "?f sums (2*w^(x+3))" by blast
    from this show ?thesis
      by (smt (verit, best) point_pow_unfold suminf_cong sums_unique)
  qed

  (* Summary of above results: inner series values for x = 0 / x > 0 *)
  from x_eq_0 x_ge_0 have x_inner_sum:
    "suminf (point_pow max_initial_coins x) = (if x = 0 then w^3 else 2*w^(x+3))" for x by simp

  (* From this, compute the outer series *)
  let ?f = "\<lambda>x. if x = 0 then w^3 else 2*w^(x+3)"

  (* Split the series in the first term (i.e. the x = 0 inner series term) and the tail series
    (i.e. the x > 0 inner series terms), since the latter all have the same form. *)
  have "(\<lambda>x. ?f (x+1)) sums s \<Longrightarrow> ?f sums (s + (\<Sum>x<1. ?f x))" for s
    using sums_iff_shift by fastforce
  then have sum_split: "(\<lambda>x. ?f (x+1)) sums s \<Longrightarrow> ?f sums (s + ?f 0)" for s by simp

  (* Compute the tail of the outer series *)
  have "(\<lambda>x. ?f (x+1)) sums (2*w^2)"
  proof -
    (* Compute the geometric sum *)
    have "?f (x+1) = 2*w^(x+1+3)" for x by simp
    then have 1: "?f (x+1) = 2*w^(4+x)" for x by auto
    have 2: "(\<lambda>x. 2*w^(4+x)) sums (2*w^4/(1-w))"
      using geometric_w_sums_transformation by simp

    (* Simplify it to 2*w^2 *)
    from 2 have "(\<lambda>x. 2*w^(4+x)) sums (2*w^4/w^2)" using w_squared by simp
    moreover have "2*w^4/w^2 = 2*w^(Suc(Suc(Suc(Suc 0))))/w^Suc(Suc 0)"
      by (simp add: numeral_2_eq_2 power4_eq_xxxx)
    then have "2*w^4/w^2 = 2*w^2" by (simp add: numeral_2_eq_2)
    ultimately have 3: "(\<lambda>x. 2*w^(4+x)) sums (2*w^2)" by simp
    from 1 3 show ?thesis by simp
  qed
  (* From the first term and the tail, compute the outer series to be 2*w^2 + w^3 *)
  then have f_sums: "?f sums (2*w^2 + w^3)" using sum_split by simp

  (* Now show that 2*w^2 + w^3 = 1 *, which concludes the proof *)
  have "2*w^2 + w^3 = w^2 + w^(2+1) + 1 - w" using w_squared by force
  moreover have "w^2 + w^(2+1) + 1 - w = w - w + 1" using w_recurrence
    by (metis add.commute diff_diff_eq2 diff_eq_eq one_add_one power_one_right)
  ultimately have two_w2_plus_w3: "2*w^2 + w^3 = 1" by auto

  from two_w2_plus_w3 f_sums have "suminf ?f = 1" using sums_unique by force 
  moreover have "power_sum max_initial_coins = suminf ?f" using x_inner_sum by simp
  ultimately show ?thesis by simp
qed

(*
  The maximal initial coin configuration is an infinite set.
*)
lemma max_initial_coins_infinite: "infinite max_initial_coins"
proof (rule ccontr)
  (* Project the set of tuples to a set of naturals *)
  let ?proj = "((\<lambda>(x, _). x) ` max_initial_coins)"

  assume "\<not>infinite max_initial_coins"
  (* If the set of tuples is finite, so is the projection *)
  then have "finite max_initial_coins" by simp
  then have "finite ?proj" by auto

  (* ?proj is non-empty and finite, so it has a maximal element k *)
  moreover have "?proj \<noteq> {}" 
  (* interesting shortcut sledgehammer found here: if max_initial_coins was empty, it would have
     `power_sum` of 0, but it has `power_sum` of 1 *)
    using finite_power_sum max_initial_coins_eq_one by force
  ultimately obtain k where max_k: "k \<in> ?proj \<and> (\<forall>j \<in> ?proj. k \<le> j \<longrightarrow> k = j)"
    using finite_has_maximal by metis

  (* But (k+1, 5) is in max_initial_coins, hence k+1 is in the projection: contradiction *)
  have "(k+1, 5) \<in> max_initial_coins" using max_initial_coins_def by auto
  then have "k+1 \<in> ?proj" by auto
  then show "False" using max_k by auto
qed

(*
  Any finite initial coin configuration has a `power_sum` less than 1.
*)
lemma initial_finite_coins_less_one:
  assumes initial: "initial_coins coins"
      and finite:"finite coins"
shows "power_sum coins < 1"
proof -
  have "coins \<subseteq> max_initial_coins" by (simp add: initial initial_coins_subset)
  (* Since `coins` is finite but `max_initial_coins` is infinite, `coins` is a proper subset *)
  moreover have "coins \<noteq> max_initial_coins" using finite max_initial_coins_infinite by blast
  ultimately have "coins \<subset> max_initial_coins" by blast
  then have "power_sum coins < power_sum max_initial_coins" using powersum_subset_less by auto
  then show ?thesis using max_initial_coins_eq_one by simp
qed

(* Any initial coin configuration has a `power_sum` of at most 1. *)
lemma initial_coins_leq_one:
  assumes "initial_coins coins"
  shows "power_sum coins \<le> 1"
  by (metis assms initial_coins_subset max_initial_coins_eq_one powersum_subset_leq)

section \<open>Power sums and jumps\<close>

(*
  A `jump` transition from one coin configuration to another weakly decreases the `power_sum`.
  (This is the second crucial property of the number w.)
*)
theorem jump_decreases_power_sum: "jump A B \<Longrightarrow> power_sum B \<le> power_sum A"
(*
  We prove this for the four directions we can jump to:
  The "left" and "right" directions are complicated because x coordinates are integers:
    we need extra cases depending on if we're on the negative side, positive side, or both
  The "up" direction is easier because y coordinates are natural numbers; we just have to take
    care when we're close to zero.
  The "down" direction is easiest because we don't even have to be careful close to zero.
*)
proof (induction rule: jump.induct)
  case (left x y A B)
  let ?x = "nat (abs x)"
  (* Show that the two power sums differ by the terms of the three coin positions that changed *)
  let ?full_diff = "w^(y + nat (abs (x-2))) - w^(y + nat (abs (x-1))) - w^(y + nat (abs x))"
  have power_sum_B: "power_sum (A - {(x, y), (x - 1, y)} \<union> {(x - 2, y)})
      = power_sum A + ?full_diff"
    using \<open>(x, y) \<in> A\<close> \<open>(x-1, y) \<in> A\<close> \<open>(x-2, y) \<notin> A\<close> power_sum_minus_singleton 
      power_sum_union_singleton
    by (smt (verit, del_insts) Diff_iff Diff_insert2 add.commute insertE insert_Diff prod.inject)

  (* Factor out w^y to simplify the remaining argument: the other factor is now called ?diff *)
  then have "?full_diff = w^y*w^(nat (abs (x-2))) - w^y*w^(nat (abs (x-1))) - w^y*w^(nat (abs x))"
    by (metis power_add)
  then have full_diff_diff: 
    "?full_diff = w^y * (w^(nat (abs (x-2))) - w^(nat (abs (x-1))) - w^(nat (abs x)))" 
    (is "?full_diff = w^y * ?diff") by (simp add: right_diff_distrib)

  (* Show that ?diff is non-positive, i.e. the power sum weakly decreases, by three cases *)
  have "?diff  \<le> 0"
  proof (cases "x \<le> 0")
    (* If x \<le> 0, a left jump goes in the direction of increasing exponents: 
      the power sum strictly decreases *)
    case x_nonpos: True
    then have "?diff = w^(?x+2) - w^(?x+1) - w^(?x)"
      by (smt (verit, ccfv_threshold) nat_1_add_1 nat_add_distrib nat_numeral numeral_eq_one_iff)
    then show ?thesis
      by (smt (verit, del_insts) w_range w_recurrence zero_less_power)
  next
    case x_pos: False
    then show ?thesis proof (cases "x \<ge> 2")
      case x_geq_2: True
      (* If x \<ge> 2, a left jump goes in the direction of decreasing exponents: 
        the power sum is unchanged because of the w recurrence relation *)
      have "?diff = w^(?x-2) - w^(?x-1) - w^(?x)" proof -
        have "nat (abs (x-2)) = ?x - 2" using x_geq_2 by (simp add: nat_diff_distrib')
        moreover have "nat (abs (x-1)) = ?x - 1" using x_geq_2 by (simp add: nat_diff_distrib')
        ultimately show ?thesis by presburger
      qed
      then have "?diff = w^(?x-2) - w^(?x-2+1) - w^(?x-2+2)"
        by (smt (verit, del_insts) Nat.add_diff_assoc2 Nat.diff_diff_right One_nat_def
            cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq' diff_zero le_add2 linorder_linear
            nat_0_iff nat_1_add_1 nat_2 nat_diff_distrib plus_1_eq_Suc x_geq_2)
      then show ?thesis by (smt (verit, ccfv_SIG) w_recurrence)
    next
      case x_eq_1: False
      (* If x = 1, a left jump crosses the x = 0 column and ?diff = w - 1 - w < 0 *)
      then have "x = 1" using x_pos by auto
      then show ?thesis by auto
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
  (* Show that the two power sums differ by the terms of the three coin positions that changed *)
  let ?full_diff = "w^(y + nat (abs (x+2))) - w^(y + nat (abs (x+1))) - w^(y + nat (abs x))"
  have power_sum_B: "power_sum (A - {(x, y), (x + 1, y)} \<union> {(x + 2, y)})
      = power_sum A + ?full_diff"
    using \<open>(x, y) \<in> A\<close> \<open>(x+1, y) \<in> A\<close> \<open>(x+2, y) \<notin> A\<close> power_sum_minus_singleton
      power_sum_union_singleton
    by (smt (z3) Diff_iff Diff_insert2 add.commute insertE insert_Diff prod.inject)

  (* Factor out w^y to simplify the remaining argument: the other factor is now called ?diff *)
  then have "?full_diff = w^y*w^(nat (abs (x+2))) - w^y*w^(nat (abs (x+1))) - w^y*w^(nat (abs x))" 
    by (metis power_add)
  then have full_diff_diff:
      "?full_diff = w^y * (w^(nat (abs (x+2))) - w^(nat (abs (x+1))) - w^(nat (abs x)))" 
    (is "?full_diff = w^y * ?diff") by (simp add: right_diff_distrib)

  (* Show that ?diff is non-positive, i.e. the power sum weakly decreases, by three cases *)
  have "?diff  \<le> 0"
  proof (cases "x \<ge> 0")
    (* If x \<ge> 0, a right jump goes in the direction of increasing exponents: 
      the power sum strictly decreases *)
    case x_nonneg: True
    then have "?diff = w^(?x+2) - w^(?x+1) - w^(?x)"
      by (smt (verit, ccfv_threshold) nat_1_add_1 nat_add_distrib nat_numeral numeral_eq_one_iff)
    then show ?thesis
      by (smt (verit, del_insts) w_range w_recurrence zero_less_power)
  next
    case x_neg: False
    then show ?thesis proof (cases "x \<le> -2")
      case x_leq_minus2: True
      (* If x \<le> -2, a right jump goes in the direction of decreasing exponents: 
        the power sum is unchanged because of the w recurrence relation *)
      have "?diff = w^(?x-2) - w^(?x-1) - w^(?x)" proof -
        have "nat (abs (x+2)) = ?x - 2" using x_leq_minus2 by (simp add: nat_diff_distrib')
        moreover have "nat (abs (x+1)) = ?x - 1" using x_leq_minus2 by (simp add: nat_diff_distrib')
        ultimately show ?thesis by presburger
      qed
      then have "?diff = w^(?x-2) - w^(?x-2+1) - w^(?x-2+2)"
        by (smt (verit, del_insts) Nat.add_diff_assoc2 Nat.diff_diff_right One_nat_def
            cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq' diff_zero le_add2 linorder_linear
            nat_0_iff nat_1_add_1 nat_2 nat_diff_distrib plus_1_eq_Suc x_leq_minus2)
      then show ?thesis by (smt (verit, ccfv_SIG) w_recurrence)
    next
      case x_eq_minus_1: False
      (* If x = -1, a right jump crosses the x = 0 column and ?diff = w - 1 - w < 0 *)   
      then have "x = -1" using x_neg by auto
      then show ?thesis by auto
    qed
  qed
  moreover have "w^y > 0" by (simp add: w_range)
  ultimately have "?full_diff \<le> 0" using full_diff_diff zero_less_mult_iff by smt
  then show ?case using right.hyps(4) by (smt (verit, best) power_sum_B)
next
  case (up x y A B)
  (*
    The "up" part is simpler (don't need to deal with crossing the x = 0 column).
  *)
  let ?x = "nat (abs x)"

  (* Show that the two power sums differ by the terms of the three coin positions that changed *)
  let ?full_diff = "w^(?x + (y-2)) - w^(?x + (y-1)) - w^(?x + y)"
  have power_sum_B: "power_sum (A - {(x, y), (x, y-1)} \<union> {(x, y-2)})
      = power_sum A + ?full_diff"
    using \<open>(x, y) \<in> A\<close> \<open>(x, y-1) \<in> A\<close> \<open>(x, y-2) \<notin> A\<close> power_sum_minus_singleton
      power_sum_union_singleton
    by (smt (verit) Diff_insert2 diff_diff_left insert_Diff insert_iff nat_1_add_1 prod.inject)

  (* Factor out w^y to simplify the remaining argument: the other factor is now called ?diff *)
  then have "?full_diff = w^(?x)*w^(y-2) - w^(?x)*w^(y-1) - w^(?x)*w^y" by (metis power_add)
  then have full_diff_diff: "?full_diff = w^(?x) * (w^(y-2) - w^(y-1) - w^y)" 
    (is "?full_diff = w^(?x) * ?diff") by (simp add: right_diff_distrib)

  (* Show that ?diff is non-positive, i.e. the power sum weakly decreases: only y \<ge> 2 is possible *)
  have "?diff  \<le> 0"
  proof (cases "y \<ge> 2")
    (* The up jump goes in the direction of decreasing exponents: the power sum is unchanged *)
    case True
    then have "?diff = w^(y-2) - w^(y-2+1) - w^(y-2+2)" using nat_le_iff_add by auto
    then have "?diff = 0" using w_recurrence[where n="y-2"] by simp
    then show ?thesis by simp
  next
    case False 
    (* This case is impossible: you cannot jump up when too close to the upper border. *)
    then have "False" using \<open>(x, y - 1) \<in> A\<close> \<open>(x, y - 2) \<notin> A\<close> by auto
    then show ?thesis ..
  qed
  moreover have "w^?x > 0" by (simp add: w_range)
  ultimately have "?full_diff \<le> 0" using full_diff_diff zero_less_mult_iff by smt
  then show ?case using up.hyps(4) by (smt (verit, best) power_sum_B)
next
  case (down x y A B)
  (*
    The "down" part is even shorter (don't need to deal with the y = 0 upper border).
  *)
  let ?x = "nat (abs x)"

  (* Show that the two power sums differ by the terms of the three coin positions that changed *)
  let ?full_diff = "w^(?x + (y+2)) - w^(?x + (y+1)) - w^(?x + y)"
  have power_sum_B: "power_sum (A - {(x, y), (x, y+1)} \<union> {(x, y+2)})
      = power_sum A + ?full_diff"
    using \<open>(x, y) \<in> A\<close> \<open>(x, y+1) \<in> A\<close> \<open>(x, y+2) \<notin> A\<close> power_sum_minus_singleton
      power_sum_union_singleton
    by (smt (verit) Diff_iff Diff_insert2 add_diff_cancel_left' diff_is_0_eq' insertE insert_Diff
        nle_le one_neq_zero prod.inject)

  (* Factor out w^y to simplify the remaining argument: the other factor is now called ?diff *)
  then have "?full_diff = w^(?x)*w^(y+2) - w^(?x)*w^(y+1) - w^(?x)*w^y" by (metis power_add)
  then have full_diff_diff: "?full_diff = w^(?x) * (w^(y+2) - w^(y+1) - w^y)" 
    (is "?full_diff = w^(?x) * ?diff") by (simp add: right_diff_distrib)

  (* Show that ?diff is non-positive, i.e. the power sum weakly decreases 
     (it actually strictly decreases: down jumps are in the direction of increasing exponents *)
  have "?diff  \<le> 0" by (smt (verit) w_range w_recurrence zero_less_power)
  moreover have "w^?x > 0" by (simp add: w_range)
  ultimately have "?full_diff \<le> 0" using full_diff_diff zero_less_mult_iff by smt
  then show ?case using down.hyps(4) by (smt (verit, best) power_sum_B)
qed

(*
  A `jumps` transition also weakly decreases the `power_sum`.
*)
corollary jumps_decrease_power_sum:
  "jumps A B \<Longrightarrow> power_sum B \<le> power_sum A"
unfolding jumps_def by (induction rule: star.induct) (fastforce dest: jump_decreases_power_sum)+

section \<open>Game unwinnable (1) (Goal field/finite initial configuration)\<close>

text \<open>This section gives the first (and weakest) version of the final theorem: We show that
  from a finite initial configuration, the goal field (0, 0) cannot be reached.
  
  The theorem is strengthened in the following sections
  - to allow any (possibly non-finite) initial configuration and
  - to show that not only the goal field (0, 0), but also no other field (x, 0) on the row y = 0
      can be reached.\<close>

(*
  The game cannot be won from a finite initial configuration, if the objective is to reach the
    goal field (0, 0).
*)
theorem finite_initial_coins_cannot_reach_goal_field:
  assumes finite: "finite A"
      and initial: "initial_coins A"
      and reaches: "jumps A B"
    shows "(0, 0) \<notin> B"
proof (rule ccontr)
  (* Assume the goal field is reached *)
  assume "\<not> (0, 0) \<notin> B"
  then have "{(0, 0)} \<subseteq> B" by simp

  (* But A has a power sum less than 1,...*)
  have "power_sum A < 1"
    using initial initial_finite_coins_less_one finite by blast
  (* ...while B has a power sum \<ge> 1... *)
  moreover have "power_sum B \<ge> 1"
    by (metis \<open>{(0, 0)} \<subseteq> B\<close> goal_field_value_1 powersum_subset_leq)
  (* ...and the power sum of B cannot be greater than that of A. Contradiction! *)
  moreover have "power_sum A \<ge> power_sum B"
    using jumps_decrease_power_sum reaches by blast
  ultimately show "False" by simp
qed

section \<open>Game unwinnable (2) (Goal row/finite initial configuration)\<close>

text \<open>This section strengthens the first version of the unwinnability theorem: we show that the
  goal field (0, 0) is not special, and that in fact no cell (x, 0) on the goal row y = 0 can be
  reached.

  We introduce a shift operation and show that any gameplay reaching a field (x, 0) can be
  shifted in order to reach (0, 0).\<close>

subsection \<open>Shift operation\<close>

(*
  Shifts a coin configuration in the x direction by some amount.
*)
fun shift :: "coins \<Rightarrow> int \<Rightarrow> coins" where
"shift coins d = {(x+d, y) |x y. (x, y) \<in> coins}"

(*
  Auxilliary lemma about sets of tuples, allows to shorten the following proofs.
*)
lemma tuple_set_eq_iff: "(\<forall>x y. ((x, y) \<in> A) = ((x, y) \<in> B)) \<Longrightarrow> A = B"
  by fastforce

(*
  Shifting back and forth by the same amount gives the original set.
*)
lemma shift_inverse: "shift (shift A d) (-d) = A" (is "?lhs = ?rhs")
  by (rule tuple_set_eq_iff) force

(*
  `shift` commutes with set differences.
*)
lemma shift_minus: "shift (A - B) d = shift A d - shift B d" (is "?lhs = ?rhs")
  by (rule tuple_set_eq_iff) force

(*
  `shift` commutes with set unions.
*)
lemma shift_union: "shift (A \<union> B) d = shift A d \<union> shift B d" (is "?lhs = ?rhs")
  by (rule tuple_set_eq_iff) force

(*
  `shift` preserves finiteness.
*)
lemma shift_finite: "finite A \<Longrightarrow> finite (shift A d)"
proof (induction rule: finite_induct)
  case (insert t F)
  obtain x y where xy: "t = (x, y)" by fastforce
  have "insert t F = F \<union> {t}" by auto
  then have "shift (insert t F) d = (shift F d) \<union> (shift {t} d)"
    using shift_union by presburger
  moreover have "shift {(x, y)} d = {(x+d, y)}" by simp
  ultimately show ?case using insert.IH xy by auto
qed simp

(*
  Auxilliary lemma to generalize an argument that will be made in each of the four jumping
    directions in the following proof.
*)
lemma jump_shift_inv_aux:
  assumes A': "A' = shift A d"
      and B': "B' = shift B d"
      and BA: "B = A - {(x1, y1), (x2, y2)} \<union> {(x3, y3)}"
    shows "B' = A' - {(x1+d, y1), (x2+d, y2)} \<union> {(x3+d, y3)}" (is "B' = A' - ?oldshift \<union> ?newshift")
proof -
  let ?old = "{(x1, y1), (x2, y2)}" (* ?old are the removed coin positions *)
  let ?new = "{(x3, y3)}" (* ?new is the added coin position *)
  from B' BA have "B' = shift (A - ?old \<union> ?new) d" by simp
  (* Use that `shift` commute with set differences and unions *)
  then have "B' = shift A d - shift ?old d \<union> shift ?new d"
    using shift_union shift_minus by presburger
  moreover have "shift ?old d = ?oldshift" by force
  moreover have "shift ?new d = ?newshift" by force
  ultimately show "B' = A' - ?oldshift \<union> ?newshift" using A' by presburger
qed

(*
  If `jump` transitions A to B, then it transitions the shifted versions A', B' as well.
*)
lemma jump_shift_inv:
  assumes "jump A B"
      and A': "A' = shift A d"
      and B': "B' = shift B d"
    shows "jump A' B'"
  using \<open>jump A B\<close> A' B' proof (induction rule: jump.induct)
(* Distinguish the four jump directions, and for each one apply the previous auxilliary lemma 
    to show that the corresponding `jump` conditions hold for the shifted versions. *)
  case (left x y A B)
  then have "(x+d, y) \<in> A' \<and> (x-1+d, y) \<in> A' \<and> (x-2+d, y) \<notin> A'" by simp
  moreover from left have "B' = A' - {(x+d, y), (x-1+d, y)} \<union> {(x-2+d, y)}" 
    using jump_shift_inv_aux by simp
  ultimately show ?case by (smt (verit, ccfv_threshold) jump.left)
next
  case (right x y A B)
  then have "(x+d, y) \<in> A' \<and> (x+1+d, y) \<in> A' \<and> (x+2+d, y) \<notin> A'" by simp
  moreover from right have "B' = A' - {(x+d, y), (x+1+d, y)} \<union> {(x+2+d, y)}" 
    using jump_shift_inv_aux by simp
  ultimately show ?case by (smt (verit, ccfv_threshold) jump.right)
next
  case (up x y A B)
  then have "(x+d, y) \<in> A' \<and> (x+d, y-1) \<in> A' \<and> (x+d, y-2) \<notin> A'" by simp
  moreover from up have "B' = A' - {(x+d, y), (x+d, y-1)} \<union> {(x+d, y-2)}" 
    using jump_shift_inv_aux by simp
  ultimately show ?case by (smt (verit, ccfv_threshold) jump.up)
next
  case (down x y A B)
  then have "(x+d, y) \<in> A' \<and> (x+d, y+1) \<in> A' \<and> (x+d, y+2) \<notin> A'" by simp
  moreover from down have "B' = A' - {(x+d, y), (x+d, y+1)} \<union> {(x+d, y+2)}"
    using jump_shift_inv_aux by simp
  ultimately show ?case by (smt (verit, ccfv_threshold) jump.down)
qed

(*
  Even stronger, `jump` transitions A to B iff it transitions A' to B'.
*)
lemma jump_shift_inv_eq:
  assumes A': "A' = shift A d"
      and B': "B' = shift B d"
    shows "jump A B \<longleftrightarrow> jump A' B'"
proof
  (* One direction was already shown, the other direction follows by shifting back *)
  show "jump A B \<Longrightarrow> jump A' B'" using A' B' jump_shift_inv by blast
  assume "jump A' B'"
  moreover have "A = shift A' (-d)" using A' shift_inverse by presburger
  moreover have "B = shift B' (-d)" using B' shift_inverse by presburger
  ultimately show "jump A B" using jump_shift_inv by blast
qed

(*
  If `jumps` transitions A to B, it also transitions `(shift A d)` to `(shift B d)`.
*)
lemma jumps_shift_inv:
  "jumps A B \<Longrightarrow> jumps (shift A d) (shift B d)"
unfolding jumps_def by (induction rule: star.induct) (meson jump_shift_inv star.simps)+

subsection \<open>Game unwinnable (2) theorem\<close>

(*
  The game cannot be won from a finite initial configuration, if the objective is to reach
    any field (x, 0) on the goal row y = 0.
*)
theorem finite_initial_coins_cannot_reach_goal_row:
  assumes finite: "finite A"
      and initial: "initial_coins A"
      and reaches: "jumps A B"
    shows "\<forall>x. (x, 0) \<notin> B"
proof (rule ccontr)
  (* Assume some field (x, 0) on the goal row is reached *)
  assume "\<not> (\<forall>x. (x, 0) \<notin> B)"
  then obtain x where "(x, 0) \<in> B" by blast

  (* Shift A and B by -x and show that now (0, 0) is reached, as well as the other conditions
       of the first version of the theorem are satisfied *)
  let ?A' = "shift A (-x)"
  let ?B' = "shift B (-x)"
  have "finite ?A'" using finite shift_finite by blast
  moreover have "initial_coins ?A'" using initial initial_coins_def by fastforce
  moreover have "(0, 0) \<in> ?B'" using \<open>(x, 0) \<in> B\<close> by force
  moreover have "jumps ?A' ?B'" using jumps_shift_inv reaches by blast

  (* Use the first version of the theorem to show the contradiction *)
  ultimately show "False" using finite_initial_coins_cannot_reach_goal_field by blast
qed

section \<open>Game unwinnable (3) (Goal field/any initial configuration)\<close>

text \<open>This section strengthens another aspect of the first version of the unwinnability theorem: 
  we show that the the finiteness assumption on the initial configuration is not needed.

  To this end, we show that a `jump` only removes a finite number of coins from the initial
  configuration. This implies that if A is an infinite initial configuration that reaches some B
  that contains the goal field, then there is still some element from A left in B. From this
  we get that the `power_sum` of such a B is strictly greater than 1.\<close>

(*
  If `jump` transitions A to B, all but a finite number of elements from A are also in B.
*)
lemma jump_keeps_cofinite_coins:
  assumes "jump A B"
    shows "\<exists>D. finite D \<and> A \<inter> B = A - D"
using \<open>jump A B\<close> proof (induction rule: jump.induct)
(* Show that only a finite number of coins change for each of the four jumping directions *)
  case (left x y A B)
  then have "A \<inter> B = A - {(x, y), (x-1, y)}" by force
  then show ?case by (meson finite.simps)
next
  case (right x y A B)
  then have "A \<inter> B = A - {(x, y), (x+1, y)}" by force
  then show ?case by (meson finite.simps)
next
  case (up x y A B)
  then have "A \<inter> B = A - {(x, y), (x, y-1)}" by force
  then show ?case by (meson finite.simps)
next
  case (down x y A B)
  then have "A \<inter> B = A - {(x, y), (x, y+1)}" by force
  then show ?case by (meson finite.simps)
qed

(*  
  Moreover, if a sequence of `jump`s transitions an infinite A to B, all but a finite number of
    elements from A are also in B.
  (We will only use that A \<inter> B is non-empty, but co-finiteness is needed to pull through the
    induction here.)
*)
lemma jumps_keeps_cofinite_coins:
  assumes reaches: "jumps A B"
      and infinite: "infinite A"
    shows "\<exists>D. finite D \<and> A \<inter> B = A - D"
  using reaches infinite unfolding jumps_def
proof (induction rule: star.induct)
  case (refl X)
  then show ?case by auto
next
  case (step X Y Z)
  (* Obtain finite sets D1 = X - (X \<inter> Y) and D2 = Y - (Y \<inter> Z) *)
  then obtain D1 where D1: "finite D1 \<and> X \<inter> Y = X - D1"
    using jump_keeps_cofinite_coins by presburger
  then have "infinite Y"
    by (metis Diff_infinite_finite finite_Int step.prems)
  from this step obtain D2 where D2: "finite D2 \<and> Y \<inter> Z = Y - D2" by blast

  (* Define a set ?D3 = X - (X \<inter> Z) *)
  let ?D3 = "X - (X \<inter> Z)"
  (* Show that the set X - (D1 \<union> D2), which is co-finite wrt. X, is contained in X \<inter> Z *)
  have "(X \<inter> Y) \<inter> (Y \<inter> Z) \<subseteq> X \<inter> Z" by blast
  moreover have "(X \<inter> Y) \<inter> (Y \<inter> Z) = X - (D1 \<union> D2)" using D1 D2 by blast
  (* From this, show that ?D3 is finite *)
  ultimately have "finite ?D3"
    by (metis D1 D2 Diff_Diff_Int Diff_Int finite_Int finite_UnI sup.absorb_iff1)
  then show ?case by blast
qed

(*
  The game cannot be won from any (possibly infinite) initial configuration, if the objective is
    to reach the goal field (0, 0).
*)
theorem initial_coins_cannot_reach_goal_field:
  assumes initial: "initial_coins A"
      and reaches: "jumps A B"
    shows "(0, 0) \<notin> B"
proof (cases "finite A")
  case True
  (* For a finite set, use the first version of the theorem *)
  then show ?thesis using finite_initial_coins_cannot_reach_goal_field initial reaches by simp
next
  case infiniteA: False
  (* For an infinite set, argue that at least one initial coin is still in place, which makes
       the power sum of B strictly greater than one if it contains the goal field *)
  show ?thesis
  proof (rule ccontr)
    (* Assume the goal field is reached *)
    assume "\<not> (0, 0) \<notin> B"
    then have "{(0, 0)} \<subseteq> B" by simp
    (* The power sum of A is \<le> 1 (but now, differently than before, possibly equal to 1) *)
    have "power_sum A \<le> 1"
      using initial initial_coins_leq_one by blast
    (* Show that the power sum of B is > 1: *)
    moreover have "power_sum B > 1"
    proof -
      (* Obtain some element (x, y) from A that is still in place in B *)
      have "\<exists>D. finite D \<and> A \<inter> B = A - D" 
        using reaches infiniteA jumps_keeps_cofinite_coins by blast
      then have "A \<inter> B \<noteq> {}" by (metis finite.emptyI finite_Diff2 infiniteA)
      then obtain x y where xy: "(x, y) \<in> A \<inter> B" by  fastforce

      (* Show that both (x, y) and (0, 0) are in B and are different *)
      then have "{(x,y), (0,0)} \<subseteq> B" using \<open>{(0, 0)} \<subseteq> B\<close> by auto
      have "(x,y) \<noteq> (0, 0)" proof -
        have "(x, y) \<in> A" using xy by simp
        then have "below_the_line (x, y)" using initial initial_coins_def by blast
        then show ?thesis by force
      qed

      (* Then show that the power sum of B is strictly greater than 1 *)
      then have "power_sum {(x,y), (0,0)} = w^(nat (abs x) + y) + 1"
        by (smt (verit) Diff_insert_absorb goal_field_value_1 insertCI insert_absorb
           power_sum_minus_singleton singleton_insert_inj_eq)
      then show ?thesis using \<open>{(x,y), (0,0)} \<subseteq> B\<close>
        by (smt (verit, ccfv_SIG) powersum_subset_leq w_range zero_less_power)
    qed
    (* Moreover, `power_sum A \<ge> power_sum B`. Contradiction! *)
    moreover have "power_sum A \<ge> power_sum B"
      using jumps_decrease_power_sum reaches by blast
    ultimately show "False" by simp
  qed
qed

section \<open>Game unwinnable (4) (Goal row/any initial configuration)\<close>

text \<open>Finally, we put the previous results together to obtain the strongest version of the
  unwinnability theorem: The goal row cannot be reached from any initial configuration.\<close>

(*
  The game cannot be won from any (possibly infinite) initial configuration, if the objective is
    to reach any field (x, 0) on the goal row y = 0.
*)
theorem initial_coins_cannot_reach_goal_row:
  assumes initial: "initial_coins A"
      and reaches: "jumps A B"
    shows "\<forall>x. (x, 0) \<notin> B"
proof (rule ccontr)
  (* Assume some field (x, 0) on the goal row is reached *)
  assume "\<not> (\<forall>x. (x, 0) \<notin> B)"
  then obtain x where "(x, 0) \<in> B" by blast

  (* Shift A and B by -x and show that now (0, 0) is reached, as well as the other conditions
       of the third version of the theorem are satisfied *)
  let ?A' = "shift A (-x)"
  let ?B' = "shift B (-x)"
  have "initial_coins ?A'" using initial initial_coins_def by fastforce
  moreover have "(0, 0) \<in> ?B'" using \<open>(x, 0) \<in> B\<close> by force
  moreover have "jumps ?A' ?B'" using jumps_shift_inv reaches by blast

  (* Use the third version of the theorem to show the contradiction *)
  ultimately show "False" using initial_coins_cannot_reach_goal_field by blast
qed


section \<open>The second-highest row can be reached\<close>

text \<open>Finally, a positive result: The second-highest row can actually be reached.
  This is shown by an example, which is minimal according to https://www.oma.org.ar/red/la_rana.htm.
\<close>

(*
  The start configuration looks like this, and has 20 coins: (Column 0 is marked with |)

      ------|----
      ..ooooooo..
      ....ooooo..
      ...oooooo..
      .....oo....
      ...........

  From this, we can reach {(0, 1)} in 19 jumps.
*)
lemma "jumps {(-1,5), (-1,6), (0,5), (0,6), (1,5), (1,6), (2,5), (2,6),(-1,7), (-1,8), (0,7), (0,8),
        (1,7), (2,7), (-2,7), (-3,7),(-2,6), (-2,5),(-3,5), (-4,5)}
      {(0,1)}"
(* The proof is in apply style as this turned out to be more convenient for this kind of proof. *)
  unfolding jumps_def
  apply (rule star.step[where y="{(-1,4),(0,5),(0,6),(1,5),(1,6),(2,5),(2,6),(-1,7),(-1,8),(0,7),
    (0,8),(1,7),(2,7),(-2,7),(-3,7),(-2,6),(-2,5),(-3,5),(-4,5)}"])
  apply (rule jump.up[of "-1" 6]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,4),(1,5),(1,6),(2,5),(2,6),(-1,7),(-1,8),(0,7),(0,8),
    (1,7),(2,7),(-2,7),(-3,7),(-2,6),(-2,5),(-3,5),(-4,5)}"])
  apply (rule jump.up[of 0 6]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,4),(1,4),(2,5),(2,6),(-1,7),(-1,8),(0,7),(0,8),(1,7),
    (2,7),(-2,7),(-3,7),(-2,6),(-2,5),(-3,5),(-4,5)}"])
  apply (rule jump.up[of 1 6]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,4),(1,4),(2,4),(-1,7),(-1,8),(0,7),(0,8),(1,7),(2,7),
    (-2,7),(-3,7),(-2,6),(-2,5),(-3,5),(-4,5)}"])
  apply (rule jump.up[of 2 6]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,4),(1,4),(2,4),(-1,6),(0,7),(0,8),(1,7),(2,7),(-2,7),
    (-3,7),(-2,6),(-2,5),(-3,5),(-4,5)}"])
  apply (rule jump.up[of "-1" 8]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,4),(1,4),(2,4),(-1,6),(0,6),(1,7),(2,7),(-2,7),(-3,7),
    (-2,6),(-2,5),(-3,5),(-4,5)}"])
  apply (rule jump.up[of "0" 8]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,4),(1,4),(2,4),(-1,6),(0,6),(0,7),(-2,7),(-3,7),(-2,6),
    (-2,5),(-3,5),(-4,5)}"])
  apply (rule jump.left[of "2" 7]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,4),(1,4),(2,4),(-1,6),(0,6),(0,7),(-1,7),(-2,6),(-2,5),
    (-3,5),(-4,5)}"])
  apply (rule jump.right[of "-3" 7]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,4),(1,4),(2,4),(-1,5),(0,6),(0,7),(-2,6),(-2,5),(-3,5),
    (-4,5)}"])
  apply (rule jump.up[of "-1" 7]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,4),(1,4),(2,4),(-1,5),(0,5),(-2,6),(-2,5),(-3,5),
    (-4,5)}"])
  apply (rule jump.up[of "0" 7]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,4),(1,4),(2,4),(-1,5),(0,5),(-2,4),(-3,5),(-4,5)}"])
  apply (rule jump.up[of "-2" 6]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,4),(1,4),(2,4),(-1,5),(0,5),(-2,4),(-2,5)}"])
  apply (rule jump.right[of "-4" 5]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,3),(1,4),(2,4),(-1,5),(-2,4),(-2,5)}"])
  apply (rule jump.up[of 0 5]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,3),(0,4),(-1,5),(-2,4),(-2,5)}"])
  apply (rule jump.left[of 2 4]) apply(force)+
  apply (rule star.step[where y="{(-1,4),(0,2),(-1,5),(-2,4),(-2,5)}"])
  apply (rule jump.up[of 0 4]) apply(force)+
  apply (rule star.step[where y="{(0,4),(0,2),(-1,5),(-2,5)}"])
  apply (rule jump.right[of "-2" 4]) apply(force)+
  apply (rule star.step[where y="{(0,4),(0,2),(0,5)}"])
  apply (rule jump.right[of "-2" 5]) apply(force)+
  apply (rule star.step[where y="{(0,3),(0,2)}"])
  apply (rule jump.up[of 0 5]) apply(force)+
  apply (rule star.step[where y="{(0,1)}"])
  apply (rule jump.up[of 0 3]) apply(force)+
  done

end