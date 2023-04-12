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

text_raw \<open>\DefineSnippet{floor_pow2_lim}{\<close>
lemma floor_pow2_lim: "(\<lambda>n. \<lfloor>2^n * T\<rfloor> / 2 ^ n) \<longlonglongrightarrow> T"
text_raw \<open>}%EndSnippet\<close>
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

text \<open> dyadic_interval_step_step n S T is the collection of dyadic numbers in {S..T} with denominator 2^n. As
 n -> \<infinity> this collection approximates {S..T}. Compare with @{thm dyadics_def}}\<close>

text_raw \<open>\DefineSnippet{dyadic_interval_step}{\<close>
definition dyadic_interval_step :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real set"
  where "dyadic_interval_step n S T \<equiv> (\<lambda>k. k / (2 ^ n)) ` {\<lceil>2^n * S\<rceil>..\<lfloor>2^n * T\<rfloor>}"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{dyadic_interval}{\<close>
definition dyadic_interval :: "real \<Rightarrow> real \<Rightarrow> real set"
  where "dyadic_interval S T \<equiv> (\<Union>n. dyadic_interval_step n S T)"
text_raw \<open>}%EndSnippet\<close>

lemma dyadic_interval_step_empty[simp]: "T < S \<Longrightarrow> dyadic_interval_step n S T = {}"
  unfolding dyadic_interval_step_def apply simp
  by (smt (verit) ceil_pow2_geq floor_le_ceiling floor_mono floor_pow2_leq
      linordered_comm_semiring_strict_class.comm_mult_strict_left_mono zero_less_power)

lemma dyadic_interval_step_0[simp]: "dyadic_interval_step n 0 0 = {0}"
  unfolding dyadic_interval_step_def by simp

lemma dyadic_interval_step_mem:
  assumes"x \<ge> 0" "T \<ge> 0" "x \<le> T" 
  shows "\<lfloor>2^n * x\<rfloor> / 2 ^ n \<in> dyadic_interval_step n 0 T"
  unfolding dyadic_interval_step_def by (simp add: assms image_iff floor_mono)

lemma dyadic_interval_step_iff: 
  "x \<in> dyadic_interval_step n S T \<longleftrightarrow>
   (\<exists>k. k \<ge> \<lceil>2^n * S\<rceil> \<and> k \<le> \<lfloor>2^n * T\<rfloor> \<and> x = k/2^n)"
  unfolding dyadic_interval_step_def by (auto simp add: image_iff)

lemma mem_dyadic_interval: "x \<in> dyadic_interval S T \<longleftrightarrow> (\<exists>n. x \<in> dyadic_interval_step n S T)"
  unfolding dyadic_interval_def by blast

lemma dyadics_leq: "x \<in> dyadic_interval_step n S T \<Longrightarrow> x \<le> T"
  unfolding dyadic_interval_step_def apply clarsimp
  by (simp add: divide_le_eq le_floor_iff mult.commute)

lemma dyadics_geq: "x \<in> dyadic_interval_step n S T \<Longrightarrow> x \<ge> S"
  unfolding dyadic_interval_step_def apply clarsimp
  by (simp add: ceiling_le_iff mult.commute pos_le_divide_eq)

corollary dyadic_interval_subset_interval: "(dyadic_interval 0 T) \<subseteq> {0..T}"
  unfolding dyadic_interval_def using dyadics_geq dyadics_leq by force

lemma zero_in_dyadics: "T \<ge> 0 \<Longrightarrow> 0 \<in> dyadic_interval_step n 0 T"
  using dyadic_interval_step_def by force

text_raw \<open>\DefineSnippet{dyadic_interval_dense}{\<close>
lemma dyadic_interval_dense: "closure (dyadic_interval 0 T) = {0..T}"
text_raw \<open>}%EndSnippet\<close>
proof (rule subset_antisym)
  have "(dyadic_interval 0 T) \<subseteq> {0..T}"
    by (fact dyadic_interval_subset_interval)
  then show "closure (dyadic_interval 0 T) \<subseteq> {0..T}"
    by (auto simp: closure_minimal)
  have "{0..T} \<subseteq> closure (dyadic_interval 0 T)" if "T \<ge> 0"
    unfolding closure_def
  proof (clarsimp)
    fix x assume x: "0 \<le> x" "x \<le> T" "x \<notin> dyadic_interval 0 T"
    then have "x > 0"
      unfolding dyadic_interval_def
      using zero_in_dyadics[OF that] order_le_less by blast
    show "x islimpt (dyadic_interval 0 T)"
      apply (simp add: islimpt_sequential)
      apply (rule exI [where x="\<lambda>n. \<lfloor>2^n * x\<rfloor> / 2^n"])
      apply safe
      using dyadic_interval_step_mem mem_dyadic_interval x(1,2) apply auto[1]
       apply (smt (verit, ccfv_threshold) dyadic_interval_step_mem mem_dyadic_interval x)
      using floor_pow2_lim apply blast
      done
  qed
  then show "{0..T} \<subseteq> closure (dyadic_interval 0 T)"
    by (cases "T \<ge> 0"; simp)
qed

lemma dyadic_interval_step_finite[simp]: "finite (dyadic_interval_step n S T)"
  unfolding dyadic_interval_step_def by simp

text_raw \<open>\DefineSnippet{dyadic_interval_countable}{\<close>
lemma dyadic_interval_countable[simp]: "countable (dyadic_interval S T)"
text_raw \<open>}%EndSnippet\<close>
  by (simp add: dyadic_interval_def dyadic_interval_step_def)

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

corollary floor_pow2_mono: "mono (\<lambda>n. \<lfloor>2^n * (T :: real)\<rfloor> / 2 ^ n)"
  apply (intro monoI)
  subgoal for x y
    using floor_pow2_add_leq[of x T "y - x"] by force
  done

lemma dyadic_interval_step_Max: "T \<ge> 0 \<Longrightarrow> Max (dyadic_interval_step n 0 T) = \<lfloor>2^n * T\<rfloor> / 2^n"
  apply (simp add: dyadic_interval_step_def)
  apply (subst mono_Max_commute[of "\<lambda>x. real_of_int x / 2^n", symmetric])
  by (auto simp: mono_def field_simps Max_eq_iff)

text_raw \<open>\DefineSnippet{dyadic_interval_step_subset}{\<close>
lemma dyadic_interval_step_subset:
  "n \<le> m \<Longrightarrow> dyadic_interval_step n 0 T \<subseteq> dyadic_interval_step m 0 T"
text_raw \<open>}%EndSnippet\<close>
proof (rule subsetI)
  fix x assume "n \<le> m" "x \<in> dyadic_interval_step n 0 T"
  then obtain k where k:  "k \<ge> 0" "k \<le> \<lfloor>2^n * T\<rfloor>" "x = k / 2^n"
    unfolding dyadic_interval_step_def by fastforce
  then have "k * 2 ^ (m - n) \<in> {0 .. \<lfloor>2^m * T\<rfloor>}"
  proof -
    have "k / 2 ^ n \<le> \<lfloor>2^m * T\<rfloor> / 2 ^ m"
      by (smt floor_pow2_mono[THEN monoD, OF \<open>n \<le> m\<close>] k(2) divide_right_mono of_int_le_iff zero_le_power)
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
  then show "x \<in> dyadic_interval_step m 0 T"
    apply (subst dyadic_interval_step_iff)
    apply (rule exI[where x="k * 2 ^ (m - n)"])
    apply simp
    apply (simp add: \<open>n \<le> m\<close> k(3) power_diff)
    done
qed

(*
fun dyadic_expansion :: "real \<Rightarrow> nat stream" where
 "dyadic_expansion k =
  (let k' = k * 2 in if k' \<ge> 1 then 1 ## dyadic_expansion (k' - 1) else 0 ## dyadic_expansion k')"

lemma dyadic_expansion_div_2: "k < 1 \<Longrightarrow> dyadic_expansion (Suc n) (k / 2) = 0 # dyadic_expansion n k"
  oops

lemma dyadic_expansion_interval:
  assumes "x \<in> dyadic_interval_step n 0 T"
  shows "of_int \<lfloor>x\<rfloor> + (\<Sum>i\<in>{0..<n}. of_nat (dyadic_expansion n x ! i) / 2 ^ Suc i) = x"
  using assms
proof (induction n)
  case 0
  then show ?case
    unfolding dyadic_interval_step_def
    by auto
next
  case (Suc n)
  then obtain k where k: "k \<in> {0..\<lfloor>2^Suc n * T\<rfloor>}" "x = k / (2 ^ Suc n)"
    unfolding dyadic_interval_step_def by force
  consider "even k" | "odd k"
    by auto
  then show ?case
  proof cases
    case 1
    then have "x = k div 2 / 2 ^ n"
      by (simp add: real_of_int_div k(2))
    moreover have "k div 2 \<in> {0..\<lfloor>2^n * T\<rfloor>}"
      using k(1) by (auto simp add: le_floor_iff)
    ultimately have "x \<in> dyadic_interval_step n 0 T"
      unfolding dyadic_interval_step_def by force
    then have "real_of_int \<lfloor>x\<rfloor> + (\<Sum>i = 0..<n. real (dyadic_expansion n x ! i) / 2 ^ Suc i) = x"
      using Suc by blast
    moreover have "dyadic_expansion (Suc n) x ! n = 0"
      sorry
    then show ?thesis sorry
  next
    case 2
    then show ?thesis sorry
  qed
qed

*)

text_raw \<open>\DefineSnippet{dyadic_expansion}{\<close>
lemma dyadic_expansion:
  assumes "x \<in> dyadic_interval_step n 0 T" 
  shows "\<exists>b k. b \<in> {1..n} \<rightarrow>\<^sub>E {0,1} \<and> k \<in> {0..\<lfloor>T\<rfloor>} \<and> x = k + (\<Sum>m\<in>{1..n}. b m / 2 ^ m)"
text_raw \<open>}%EndSnippet\<close>
  using assms
proof (induction n arbitrary: x)
  case 0
  then have "x \<in> {0..\<lfloor>T\<rfloor>}"
    unfolding dyadic_interval_step_def by auto
  then show ?case
    using 0 dyadic_interval_step_iff by simp
next
  case (Suc n)
  then obtain k where k: "k \<in> {0..\<lfloor>2 ^ (Suc n) * T\<rfloor>}" "x = k / 2 ^ (Suc n)"
    unfolding dyadic_interval_step_def by fastforce
  then have div2: "k div 2 \<in> {0..\<lfloor>2 ^ n * T\<rfloor>}"
      using k(1) apply simp
      by (metis divide_le_eq_numeral1(1) floor_divide_of_int_eq floor_mono le_floor_iff mult.assoc mult.commute of_int_numeral)
  then show ?case
  proof (cases "even k")
    case True
    then have "x = k div 2 / 2 ^ n"
      by (simp add: k(2) real_of_int_div)
    then have "x \<in> dyadic_interval_step n 0 T"
      using dyadic_interval_step_def div2 by force
    then obtain k' b where kb: "b \<in> {1..n} \<rightarrow>\<^sub>E {0, 1}" "k' \<in> {0..\<lfloor>T\<rfloor>}" "x = real_of_int k' + (\<Sum>m\<in>{1..n}. b m / 2 ^ m)"
      using Suc(1) by blast
    show ?thesis
      apply (rule exI[where x="b(Suc n := 0)"])
      apply (rule exI[where x="k'"])
      apply safe
      using kb(1) apply fastforce
      apply (metis PiE_arb atLeast0_atMost_Suc atLeast0_atMost_Suc_eq_insert_0 atLeastAtMost_iff atMost_atLeast0 fun_upd_other image_Suc_atMost insert_iff kb(1) nat.simps(3))
      using kb(2) apply fastforce
      apply (simp add: kb(3))
      done
  next
    case False
    then have "k = 2 * (k div 2) + 1"
      by force
    then have "x = k div 2 / 2 ^ n + 1 / 2 ^ (Suc n)"
      by (simp add: k(2) field_simps)
    then have "x - 1 / 2 ^ (Suc n) \<in> dyadic_interval_step n 0 T"
      using div2 by (simp add: dyadic_interval_step_def)
    then obtain k' b where kb: "b \<in> {1..n} \<rightarrow>\<^sub>E {0, 1}" "k' \<in> {0..\<lfloor>T\<rfloor>}" "x - 1/2^Suc n = real_of_int k' + (\<Sum>m\<in>{1..n}. b m / 2 ^ m)"
      using Suc(1)[of "x - 1 / 2 ^ (Suc n)"] by blast
    have x: "x = real_of_int k' + (\<Sum>m\<in>{1..n}. b m / 2 ^ m) + 1/2^Suc n"
      using kb(3) by (simp add: field_simps)
    show ?thesis
      apply (rule exI[where x="b(Suc n := 1)"])
      apply (rule exI[where x="k'"])
      apply safe
      using kb(1) apply fastforce
      apply (metis PiE_arb atLeast0_atMost_Suc atLeast0_atMost_Suc_eq_insert_0 atLeastAtMost_iff atMost_atLeast0 fun_upd_other image_Suc_atMost insert_iff kb(1) nat.simps(3))
     using kb(2) apply blast
      using x by simp
  qed
qed

end
