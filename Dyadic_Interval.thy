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

lemma dyadic_interval_step_singleton[simp]: "X \<in> \<int> \<Longrightarrow> dyadic_interval_step n X X = {X}"
proof -
  assume "X \<in> \<int>"
  then have *: "\<lfloor>2 ^ k * X\<rfloor> = 2 ^ k * X" for k :: nat
    by simp
  then show ?thesis
    unfolding dyadic_interval_step_def apply (simp add: ceiling_altdef)
    using * by presburger
qed

lemma dyadic_interval_step_zero[simp]: "dyadic_interval_step 0 S T = real_of_int ` {\<lceil>S\<rceil> .. \<lfloor>T\<rfloor>}"
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

lemma dyadic_as_natural:
  assumes "x \<in> dyadic_interval_step n 0 T"
  shows "\<exists>!k. x = real k / 2 ^ n"
  using assms
proof (induct n)
  case 0
  then show ?case
    apply simp
    by (metis 0 ceiling_zero div_by_1 dyadic_interval_step_iff mult_not_zero of_nat_eq_iff of_nat_nat power.simps(1))
next
  case (Suc n)
  then show ?case
      by (auto simp: dyadic_interval_step_iff, metis of_nat_nat)
  qed

lemma dyadic_times_nat: "x \<in> dyadic_interval_step n 0 T \<Longrightarrow> (x * 2 ^ n) \<in> \<nat>"
  using dyadic_as_natural by fastforce

definition "is_dyadic_expansion x n T b k \<equiv> set b \<subseteq> {0,1}
  \<and> length b = n \<and> k \<in> {0..\<lfloor>T\<rfloor>} \<and> x = k + (\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m)"

lemma is_dyadic_expansionI:
  assumes "set b \<subseteq> {0,1}" "length b = n" "k \<in> {0..\<lfloor>T\<rfloor>}" "x= k + (\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m)"
  shows "is_dyadic_expansion x n T b k"
  unfolding is_dyadic_expansion_def using assms by blast

lemma is_dyadic_expansionD:
  assumes "is_dyadic_expansion x n T b k"
  shows "set b \<subseteq> {0,1}"
    and "length b = n"
    and "k \<in> {0..\<lfloor>T\<rfloor>}"
    and "x = k + (\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m)"
  using assms unfolding is_dyadic_expansion_def by simp_all

text_raw \<open>\DefineSnippet{dyadic_expansion}{\<close>
lemma dyadic_expansion:
  assumes "x \<in> dyadic_interval_step n 0 T" 
  shows "\<exists>b k. is_dyadic_expansion x n T b k"
text_raw \<open>}%EndSnippet\<close>
  using assms unfolding is_dyadic_expansion_def
proof (induction n arbitrary: x)
  case 0
  then show ?case
    by force
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
    then obtain k' b where kb: "set b \<subseteq> {0, 1}" "length b = n" "k' \<in> {0..\<lfloor>T\<rfloor>}" "x = real_of_int k' + (\<Sum>m = 1..n. b ! (m-1) / 2 ^ m)"
      using Suc(1) by blast
    show ?thesis
      apply (rule exI[where x="b @ [0]"])
      apply (rule exI[where x="k'"])
      apply safe
      using kb apply auto
      apply (intro sum.cong)
      apply (auto simp: nth_append)
      done
  next
    case False
    then have "k = 2 * (k div 2) + 1"
      by force
    then have "x = k div 2 / 2 ^ n + 1 / 2 ^ (Suc n)"
      by (simp add: k(2) field_simps)
    then have "x - 1 / 2 ^ (Suc n) \<in> dyadic_interval_step n 0 T"
      using div2 by (simp add: dyadic_interval_step_def)
    then obtain k' b where kb: "set b \<subseteq> {0, 1}" "length b = n" "k' \<in> {0..\<lfloor>T\<rfloor>}" "x - 1/2^Suc n = real_of_int k' + (\<Sum>m = 1..n. b ! (m-1) / 2 ^ m)"
      using Suc(1)[of "x - 1 / 2 ^ (Suc n)"] by blast
    have x: "x = real_of_int k' + (\<Sum>m = 1..n. b ! (m-1) / 2 ^ m) + 1/2^Suc n"
      using kb(4) by (simp add: field_simps)
    show ?thesis
      apply (rule exI[where x="b @ [1]"])
      apply (rule exI[where x="k'"])
      apply safe
      using kb x apply auto
      apply (intro sum.cong)
       apply (auto simp: nth_append)
      done
  qed
qed

lemma dyadic_expansion_frac_le_1: 
  assumes "is_dyadic_expansion x n T b k"
  shows "(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) < 1"
proof -
  have "b ! (m - 1) \<in> {0,1}" if "m \<in> {1..n}" for m
  proof -
    from assms have "set b \<subseteq> {0,1}" "length b = n"
      unfolding is_dyadic_expansion_def by blast+
    then have "a < n \<Longrightarrow> b ! a \<in> {0,1}" for a
      by force
    moreover have "m - 1 < n"
      using that by force
    ultimately show ?thesis
      by blast
  qed
  then have "(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) \<le> (\<Sum>m\<in>{1..n}. 1 / 2 ^ m)"
    apply (intro sum_mono)
    using assms by fastforce
  also have "... = 1 - 1/2^n"
    by (induct n, auto)
  finally show ?thesis
    by (smt (verit, ccfv_SIG) add_divide_distrib divide_strict_right_mono zero_less_power)
qed

lemma dyadic_expansion_frac_range:
  assumes "is_dyadic_expansion x n T b k" "m \<in> {1..n}"
  shows "b ! (m-1) \<in> {0,1}"
proof -
  have "m - 1 < length b"
    using is_dyadic_expansionD(2)[OF assms(1)] assms(2) by fastforce
  then show ?thesis
    using nth_mem is_dyadic_expansionD(1)[OF assms(1)] by blast
qed

lemma dyadic_expansion_frac_geq_0:
  assumes "is_dyadic_expansion x n T b k"
  shows "(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) \<ge> 0"
proof -
  have "b ! (m - 1) \<in> {0,1}" if "m \<in> {1..n}" for m
    using dyadic_expansion_frac_range[OF assms] that by blast
  then have "(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) \<ge> (\<Sum>m\<in>{1..n}. 0)"
    by (intro sum_mono, fastforce)
  then show ?thesis
    by auto
qed

lemma sum_interval_pow2_inv: "(\<Sum>m\<in>{Suc l..n}. (1 :: real) / 2 ^ m) = 1 / 2^l - 1/2^n" if "l < n"
  using that proof (induct l)
  case 0
  then show ?case
    by (induct n; fastforce)
next
  case (Suc l)
  have "(\<Sum>m\<in>{Suc l..n} - {Suc l}. (1::real) / 2 ^ m) = (\<Sum>m = Suc l..n. 1 / 2 ^ m) - 1 / 2 ^ Suc l"
    using Suc by (auto simp add: Suc sum_diff1, linarith)
  moreover have "{Suc l..n} - {Suc l} = {Suc (Suc l)..n}" 
    by fastforce
  ultimately have "(\<Sum>m = Suc (Suc l)..n. (1::real) / 2 ^ m) = (\<Sum>m = (Suc l)..n. 1 / 2 ^ m) - 1 / 2^(Suc l)"
    by force
  also have "... = 1 / 2 ^ l - 1 / 2 ^ n - 1 / 2^(Suc l)"
    using Suc by linarith
  also have "... = 1 / 2 ^ Suc l - 1 / 2 ^ n"
    by (simp add: field_simps)
  finally show ?case
    by blast
qed

lemma dyadic_expansion_unique:
  assumes "is_dyadic_expansion x n T b k"
      and "is_dyadic_expansion x n T c j"
    shows "b = c \<and> j = k"
proof (rule ccontr)
  assume "\<not> (b = c \<and> j = k)"
  then consider (jk) "j \<noteq> k" | (bc) "b \<noteq> c \<and> j = k"
    by blast
  then show False
  proof cases
    case jk then have "j < k \<or> k < j"
      by linarith
    then show False
      by (smt (verit) dyadic_expansion_frac_geq_0 dyadic_expansion_frac_le_1 is_dyadic_expansionD(4)
          assms int_less_real_le)
  next
    case bc
    then have eq: "(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) = (\<Sum>m\<in>{1..n}. (c ! (m-1)) / 2 ^ m)"
    proof -
      have "k + (\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) = j + (\<Sum>m\<in>{1..n}. (c ! (m-1)) / 2 ^ m)"
        using assms is_dyadic_expansionD(4) by blast
      then show ?thesis
        using bc by linarith
    qed
    have ex: "\<exists>l < n. b ! l \<noteq> c ! l"
      by (metis list_eq_iff_nth_eq assms bc is_dyadic_expansionD(2))
    define l where "l \<equiv> LEAST l. l < n \<and> b ! l \<noteq> c ! l"
    then have l: "l < n" "b ! l \<noteq> c ! l"
      unfolding l_def using LeastI_ex[OF ex] by blast+
    have less_l: "b ! k = c ! k" if \<open>k < l\<close> for k
    proof -
      have "k < n"
        using that l by linarith
      then show "b ! k = c ! k"
        using that unfolding l_def using not_less_Least by blast
    qed
    then have "l \<in> {0..n-1}"
      using l by simp
    then have "l < n"
      apply (simp add: algebra_simps)
      using ex by fastforce
    then have "b ! l \<in> {0,1}" "c ! l \<in> {0,1}"
      by (metis assms insert_absorb insert_subset is_dyadic_expansionD(1,2) nth_mem)+
    then consider "b ! l = 0 \<and> c ! l = 1" | "b ! l = 1 \<and> c ! l = 0"
      by (smt (verit) LeastI_ex emptyE insertE l_def ex)
    then have sum_ge_l_noteq:"(\<Sum>m\<in>{l+1..n}. (b ! (m-1)) / 2 ^ m) \<noteq> (\<Sum>m\<in>{l+1..n}. (c ! (m-1)) / 2 ^ m)"
    proof cases
      case 1
      have *: ?thesis if "l + 1 = n"
        using that 1 by auto
      {
        assume \<open>l + 1 < n\<close>
        have "(\<Sum>m\<in>{l+1..n}. (c ! (m-1)) / 2 ^ m) =  (c ! ((l+1)-1)) / 2 ^ (l+1) + (\<Sum>m\<in>{Suc (l+1)..n}. (c ! (m-1)) / 2 ^ m)"
          by (smt (verit, ccfv_SIG) Suc_eq_plus1 Suc_le_mono Suc_pred' \<open>l \<in> {0..n - 1}\<close> atLeastAtMost_iff bot_nat_0.not_eq_extremum ex order_less_trans sum.atLeast_Suc_atMost)
        also have "... \<ge> 1 / 2 ^ (l+1)"
          apply (simp add: 1)
          apply (rule sum_nonneg)
          using dyadic_expansion_frac_range[OF assms(2)] apply (simp add: field_simps)
          by (metis One_nat_def gr_implies_not0 leI le_numeral_extra(3) less_one linordered_nonzero_semiring_class.zero_le_one nat_less_le old.nat.distinct(2))
        finally have c_ge: "(\<Sum>m\<in>{l+1..n}. (c ! (m-1)) / 2 ^ m) \<ge> 1/2^(l+1)" .
        have "(\<Sum>m\<in>{l+1..n}. (b ! (m-1)) / 2 ^ m) =  (b ! ((l+1)-1)) / 2 ^ (l+1) + (\<Sum>m\<in>{Suc (l+1)..n}. (b ! (m-1)) / 2 ^ m)"
          by (smt (verit, ccfv_SIG) Suc_eq_plus1 Suc_le_mono Suc_pred' \<open>l \<in> {0..n - 1}\<close> atLeastAtMost_iff bot_nat_0.not_eq_extremum ex order_less_trans sum.atLeast_Suc_atMost)
        also have "... = (\<Sum>m\<in>{Suc (l+1)..n}. (b ! (m-1)) / 2 ^ m)"
          using 1 by auto
        also have "... \<le> (\<Sum>m\<in>{Suc (l+1)..n}. 1 / 2 ^ m)"
          apply (rule sum_mono)
          using dyadic_expansion_frac_range[OF assms(1)] apply (simp add: field_simps)
          by (metis Suc_eq_plus1 add_diff_cancel_left' diff_le_self dual_order.refl not_less_eq_eq old.nat.exhaust zero_less_one_class.zero_le_one)
        also have "... < 1 / 2 ^ (l+1)"
          using sum_interval_pow2_inv[OF \<open>l + 1 < n\<close>] by fastforce
        finally have "(\<Sum>m\<in>{l+1..n}. (b ! (m-1)) / 2 ^ m) < 1 / 2 ^ (l+1)" .
        with c_ge have ?thesis
          by argo
      }
      then show ?thesis
        using * \<open>l < n\<close> by linarith
    next
      case 2 (* Copied and pasted from above - WLOG argument *)
      have *: ?thesis if "l + 1 = n"
        using that 2 by auto
      {
        assume \<open>l + 1 < n\<close>
        have "(\<Sum>m\<in>{l+1..n}. (b ! (m-1)) / 2 ^ m) =  (b ! ((l+1)-1)) / 2 ^ (l+1) + (\<Sum>m\<in>{Suc (l+1)..n}. (b ! (m-1)) / 2 ^ m)"
          by (smt (verit, ccfv_SIG) Suc_eq_plus1 Suc_le_mono Suc_pred' \<open>l \<in> {0..n - 1}\<close> atLeastAtMost_iff bot_nat_0.not_eq_extremum ex order_less_trans sum.atLeast_Suc_atMost)
        also have "... \<ge> 1 / 2 ^ (l+1)"
          apply (simp add: 2)
          apply (rule sum_nonneg)
          using dyadic_expansion_frac_range[OF assms(1)] apply (simp add: field_simps)
          by (metis One_nat_def gr_implies_not0 leI le_numeral_extra(3) less_one linordered_nonzero_semiring_class.zero_le_one nat_less_le old.nat.distinct(2))
        finally have b_ge: "(\<Sum>m\<in>{l+1..n}. (b ! (m-1)) / 2 ^ m) \<ge> 1/2^(l+1)" .
        have "(\<Sum>m\<in>{l+1..n}. (c ! (m-1)) / 2 ^ m) =  (c ! ((l+1)-1)) / 2 ^ (l+1) + (\<Sum>m\<in>{Suc (l+1)..n}. (c ! (m-1)) / 2 ^ m)"
          by (smt (verit, ccfv_SIG) Suc_eq_plus1 Suc_le_mono Suc_pred' \<open>l \<in> {0..n - 1}\<close> atLeastAtMost_iff bot_nat_0.not_eq_extremum ex order_less_trans sum.atLeast_Suc_atMost)
        also have "... = (\<Sum>m\<in>{Suc (l+1)..n}. (c ! (m-1)) / 2 ^ m)"
          using 2 by auto
        also have "... \<le> (\<Sum>m\<in>{Suc (l+1)..n}. 1 / 2 ^ m)"
          apply (rule sum_mono)
          using dyadic_expansion_frac_range[OF assms(2)] apply (simp add: field_simps)
          by (metis Suc_eq_plus1 add_diff_cancel_left' diff_le_self dual_order.refl not_less_eq_eq old.nat.exhaust zero_less_one_class.zero_le_one)
        also have "... < 1 / 2 ^ (l+1)"
          using sum_interval_pow2_inv[OF \<open>l + 1 < n\<close>] by fastforce
        finally have "(\<Sum>m\<in>{l+1..n}. (c ! (m-1)) / 2 ^ m) < 1 / 2 ^ (l+1)" .
        with b_ge have ?thesis
          by argo
      }
      then show ?thesis
        using * \<open>l < n\<close> by linarith
    qed
    moreover have sum_upto_l_eq: "(\<Sum>m\<in>{1..l}. (b ! (m-1)) / 2 ^ m) = (\<Sum>m\<in>{1..l}. (c ! (m-1)) / 2 ^ m)"
      apply (rule sum.cong)
       apply auto
      by (smt (verit, best) Suc_le_eq Suc_pred \<open>l < n\<close> l_def not_less_Least order_less_trans)
    ultimately have "(\<Sum>m\<in>{1..n}. (b ! (m-1)) / 2 ^ m) \<noteq> (\<Sum>m\<in>{1..n}. (c ! (m-1)) / 2 ^ m)"
    proof -
      have split: "{1..n} = {1..l} \<union> {l<..n}"
        using \<open>l < n\<close> by auto
      have disj: "{1..l} \<inter> {l<..n} = {}"
        using ivl_disj_int_two(8) by blast
      have "(\<Sum>m \<in>{1..n}. (b ! (m-1)) / 2 ^ m) = (\<Sum>m =1..l. (b ! (m-1)) / 2 ^ m) + (\<Sum>m \<in> {l<..n}. (b ! (m-1)) / 2 ^ m)"
        apply (subst split)
        using disj by (simp add: sum_Un)
      moreover have "(\<Sum>m \<in>{1..n}. (c ! (m-1)) / 2 ^ m) = (\<Sum>m =1..l. (c ! (m-1)) / 2 ^ m) + (\<Sum>m \<in> {l<..n}. (c ! (m-1)) / 2 ^ m)"
        apply (subst split)
        using disj by (simp add: sum_Un)
      ultimately show ?thesis
        using sum_upto_l_eq sum_ge_l_noteq
        by (smt (verit, del_insts) Suc_eq_plus1 atLeastSucAtMost_greaterThanAtMost)
    qed
    then show False
      using eq by blast
  qed
qed

end
