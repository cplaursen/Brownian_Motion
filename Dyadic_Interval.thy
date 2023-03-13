theory Dyadic_Interval
  imports "HOL-Analysis.Analysis"
begin

text \<open> In this file we describe intervals of dyadic numbers {S..T} for reals S T. We use the floor
  and ceiling functions to approximate the numbers with increasing accuracy. \<close>

lemma frac_floor: "\<lfloor>x\<rfloor> = x - frac x"
  by (simp add: frac_def)

lemma frac_ceil: "\<lceil>x\<rceil> = x + frac (- x)"
  apply (simp add: frac_neg)
  unfolding frac_def
  by (smt (verit, del_insts) Ints_of_int ceiling_altdef of_int_1 of_int_add)

lemma floor_pow2_lim: "(\<lambda>n. \<lfloor>2^n * T\<rfloor> / 2 ^ n) \<longlonglongrightarrow> T"
proof (intro LIMSEQ_I)
  fix r :: real assume "r > 0"
  obtain k where k: "1 / 2^k < r"
    by (metis \<open>r > 0\<close> one_less_numeral_iff power_one_over reals_power_lt_ex semiring_norm(76))
  then have "\<forall>n\<ge>k. norm (\<lfloor>2 ^ n * T\<rfloor> / 2 ^ n - T) < r"
    apply (simp add: frac_floor field_simps)
    by (smt (verit, ccfv_SIG) \<open>0 < r\<close> frac_lt_1 mult_left_mono power_increasing)
  then show "\<exists>no. \<forall>n\<ge>no. norm (real_of_int \<lfloor>2 ^ n * T\<rfloor> / 2 ^ n - T) < r"
    by blast
qed

lemma floor_pow2_leq: "\<lfloor>2^n * T\<rfloor> / 2 ^ n \<le> T"
  by (simp add: frac_floor field_simps)
 
lemma ceil_pow2_lim: "(\<lambda>n. \<lceil>2^n * T\<rceil> / 2 ^ n) \<longlonglongrightarrow> T"
proof (intro LIMSEQ_I)
  fix r :: real assume "r > 0"
  obtain k where k: "1 / 2^k < r"
    by (metis \<open>r > 0\<close> one_less_numeral_iff power_one_over reals_power_lt_ex semiring_norm(76))
  then have "\<forall>n\<ge>k. norm (\<lceil>2 ^ n * T\<rceil> / 2 ^ n - T) < r"
    apply (simp add: frac_ceil field_simps)
    by (smt (verit) \<open>0 < r\<close> frac_lt_1 mult_left_mono power_increasing)
  then show "\<exists>no. \<forall>n\<ge>no. norm (\<lceil>2 ^ n * T\<rceil> / 2 ^ n - T) < r"
    by blast 
qed

lemma ceil_pow2_geq: "\<lceil>2^n * T\<rceil> / 2 ^ n \<ge> T"
  by (simp add: frac_ceil field_simps)

text \<open> dyadic_interval n T is the collection of dyadic numbers in {S..T} with denominator 2^n. As
 n -> \<infinity> this collection approximates {S..T}. \<close>

definition dyadic_interval :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real set"
  where "dyadic_interval n S T \<equiv> (\<lambda>k. k / (2 ^ n)) ` {\<lceil>2^n * S\<rceil>..\<lfloor>2^n * T\<rfloor>}" 

lemma dyadic_interval_empty[simp]: "T < S \<Longrightarrow> dyadic_interval n S T = {}"
  unfolding dyadic_interval_def apply simp
  by (smt (verit) ceil_pow2_geq floor_le_ceiling floor_mono floor_pow2_leq linordered_comm_semiring_strict_class.comm_mult_strict_left_mono zero_less_power)

lemma dyadic_interval_0[simp]: "dyadic_interval n 0 0 = {0}"
  unfolding dyadic_interval_def by simp

lemma dyadic_interval_mem:
  assumes"x \<ge> 0" "T \<ge> 0" "x \<le> T" 
  shows "\<lfloor>2^n * x\<rfloor> / 2 ^ n \<in> dyadic_interval n 0 T"
  unfolding dyadic_interval_def by (simp add: assms image_iff floor_mono)

lemma dyadic_interval_iff: "x \<in> dyadic_interval n S T \<longleftrightarrow> (\<exists>k. k \<ge> \<lceil>2^n * S\<rceil> \<and> k \<le> \<lfloor>2^n * T\<rfloor> \<and> x = k/2^n)"
  unfolding dyadic_interval_def by (auto simp add: image_iff)

lemma dyadics_leq: "x \<in> dyadic_interval n S T \<Longrightarrow> x \<le> T"
  unfolding dyadic_interval_def apply clarsimp
  by (simp add: divide_le_eq le_floor_iff mult.commute)

lemma dyadics_geq: "x \<in> dyadic_interval n S T \<Longrightarrow> x \<ge> S"
  unfolding dyadic_interval_def apply clarsimp
  by (simp add: ceiling_le_iff mult.commute pos_le_divide_eq)

lemma zero_in_dyadics: "T \<ge> 0 \<Longrightarrow> 0 \<in> dyadic_interval n 0 T"
  using dyadic_interval_def by force

lemma dyadic_interval_dense: "closure (\<Union>n. dyadic_interval n 0 T) = {0..T}"
proof (rule subset_antisym)
  have "(\<Union>n. dyadic_interval n 0 T) \<subseteq> {0..T}"
    using dyadics_leq dyadics_geq by force
  then show "closure (\<Union>n. dyadic_interval n 0 T) \<subseteq> {0..T}"
    by (auto simp: closure_minimal)
  have "{0..T} \<subseteq> closure (\<Union>n. dyadic_interval n 0 T)" if "T \<ge> 0"
    unfolding closure_def
  proof (clarsimp)
    fix x assume x: "0 \<le> x" "x \<le> T" "\<forall>n. x \<notin> dyadic_interval n 0 T"
    then have "x > 0"
      using zero_in_dyadics[OF that] order_le_less by blast
    show "x islimpt (\<Union>n. dyadic_interval n 0 T)"
      apply (simp add: islimpt_sequential)
      apply (rule exI [where x="\<lambda>n. \<lfloor>2^n * x\<rfloor> / 2^n"])
      apply safe
        using that dyadic_interval_mem x(1,2) apply blast
        apply (smt (verit) dyadic_interval_mem x)
        apply (fact floor_pow2_lim)
      done
  qed
  then show "{0..T} \<subseteq> closure (\<Union>n. dyadic_interval n 0 T)"
    by (cases "T \<ge> 0"; simp)
qed

lemma dyadic_interval_finite[simp]: "finite (dyadic_interval n S T)"
  unfolding dyadic_interval_def by simp

lemma dyadic_interval_countable[simp]: "countable (\<Union>n. dyadic_interval n S T)"
  by (simp add: dyadic_interval_def)

lemma floor_pow2_add_leq:
  fixes T :: real
  shows "\<lfloor>2^n * T\<rfloor> / 2 ^ n \<le> \<lfloor>2 ^ (n+k) * T\<rfloor> / 2 ^ (n+k)"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  let ?f = "frac (2 ^ (n + k) * T)"
  and ?f' = "frac (2 ^ (n + (Suc k)) * T)"
  show ?case
  proof (cases "?f < 1/2")
    case True
    then have "?f + ?f < 1"
      by auto
    then have "frac ((2 ^ (n + k) * T) + (2 ^ (n + k) * T)) = ?f + ?f"
      using frac_add by meson
    then have "?f' = ?f + ?f"
      by (simp add: field_simps)
    then have "\<lfloor>2 ^ (n + Suc k) * T\<rfloor> / 2 ^ (n + Suc k) = \<lfloor>2^(n + k) * T\<rfloor> / 2 ^ (n + k)"
      by (simp add: frac_def)
    then show ?thesis
      using Suc by presburger
  next
    case False
    have "?f' = frac (2 ^ (n + k) * T + 2 ^ (n + k) * T)"
      by (simp add: field_simps)
    then have "?f' = 2 * ?f - 1"
      by (smt (verit, del_insts) frac_add False field_sum_of_halves)
    then have "?f' < ?f"
      using frac_lt_1 by auto
    then have "(2 ^ (n + k) * T - ?f) / 2 ^ (n + k) < (2 ^ (n + (Suc k)) * T - ?f') / 2 ^ (n + Suc k)"
      apply (simp add: field_simps)
      by (smt (verit, ccfv_threshold) frac_ge_0)
    then show ?thesis
      by (smt (verit, ccfv_SIG) Suc frac_def)
  qed
qed

corollary mono_floor_pow2: "mono (\<lambda>n. \<lfloor>2^n * (T :: real)\<rfloor> / 2 ^ n)"
  apply (intro monoI)
  subgoal for x y
    using floor_pow2_add_leq[of x T "y - x"] by force
  done

lemma dyadic_interval_subset: "n \<le> m \<Longrightarrow> dyadic_interval n 0 T \<subseteq> dyadic_interval m 0 T"
proof (rule subsetI)
  fix x assume "n \<le> m" "x \<in> dyadic_interval n 0 T"
  then obtain k where k:  "k \<ge> 0" "k \<le> \<lfloor>2^n * T\<rfloor>" "x = k / 2^n"
    unfolding dyadic_interval_def by fastforce
  then have "k * 2 ^ (m - n) \<in> {0 .. \<lfloor>2^m * T\<rfloor>}"
  proof -
    have "k / 2 ^ n \<le> \<lfloor>2^m * T\<rfloor> / 2 ^ m"
      by (smt mono_floor_pow2[THEN monoD, OF \<open>n \<le> m\<close>] k(2) divide_right_mono of_int_le_iff zero_le_power)
    then have "k / 2 ^ n * 2 ^ m \<le> \<lfloor>2^m * T\<rfloor>"
      by (simp add: field_simps)
    moreover have "k / 2 ^ n * 2 ^ m = k * 2 ^ (m - n)"
      apply (simp add: field_simps)
      apply (metis \<open>n \<le> m\<close> add_diff_inverse_nat not_less power_add)
      done
    ultimately have "k * 2 ^ (m - n) \<le> \<lfloor>2^m * T\<rfloor>"
      by linarith
    then show "k * 2 ^ (m - n) \<in> {0 .. \<lfloor>2^m * T\<rfloor>}"
      using k(1) by simp
  qed
  then show "x \<in> dyadic_interval m 0 T"
    apply (subst dyadic_interval_iff)
    apply (rule exI[where x="k * 2 ^ (m - n)"])
    apply simp
    apply (simp add: \<open>n \<le> m\<close> k(3) power_diff)
    done
qed

end