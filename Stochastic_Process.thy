theory Stochastic_Process
  imports Filtration Explorer.Explorer
begin

text \<open> A stochastic process is an indexed collection of random variables. For compatibility with 
  product_prob_space we don't mention the index set I in the assumptions. \<close>

locale stochastic_process = prob_space +
  fixes M' :: "'b measure"
    and I :: "'t set"
    and X :: "'t \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes random_X: "\<And>i. random_variable M' (X i)"

sublocale stochastic_process \<subseteq> prod: product_prob_space "(\<lambda>t. distr M M' (X t))"
  using prob_space_distr random_X by (blast intro: product_prob_spaceI)

context stochastic_process begin

text \<open> We define the finite-dimensional distributions of our process. \<close>

definition distributions :: "'t set \<Rightarrow> ('t \<Rightarrow> 'b) measure" where
"distributions T = (\<Pi>\<^sub>M t\<in>T. distr M M' (X t))"

lemma prob_space_distributions: "prob_space (distributions J)"
  by (simp add: distributions_def local.prod.prob_space prob_space_PiM)

lemma sets_distributions: "sets (distributions J) = sets (PiM J (\<lambda>_. M'))"
  unfolding distributions_def by (rule sets_PiM_cong; simp)

lemma space_distributions: "space (distributions J) = (\<Pi>\<^sub>E i\<in>J. space M')"
  unfolding distributions_def by (simp add: space_PiM)

lemma emeasure_distributions:
  assumes "finite J" "\<And>j. j\<in>J \<Longrightarrow> A j \<in> sets M'"
  shows "emeasure (distributions J) (Pi\<^sub>E J A) = (\<Prod>j\<in>J. emeasure (distr M M' (X j)) (A j))"
  by (simp add: distributions_def assms prod.emeasure_PiM)
end

sublocale stochastic_process \<subseteq> projective_family I distributions "(\<lambda>_. M')"
proof (intro projective_family.intro)
  fix J and H
  assume *: "J \<subseteq> H" "finite H" "H \<subseteq> I"
  then have "J \<subseteq> I"
    by simp
  show "distributions J = distr (distributions H) (Pi\<^sub>M J (\<lambda>_. M')) (\<lambda>f. restrict f J)"
  proof (rule measure_eqI)
    show "sets (distributions J) = sets (distr (distributions H) (Pi\<^sub>M J (\<lambda>_. M')) (\<lambda>f. restrict f J))"
      by (simp add: sets_distributions)
    fix S assume "S \<in> sets (distributions J)"
    then have in_sets: "S \<in> sets (PiM J (\<lambda>_. M'))"
      by (simp add: sets_distributions)
    have prod_emb_distr: "(prod_emb H (\<lambda>_. M') J S) = (prod_emb H (\<lambda>t. distr M M' (X t)) J S)"
      by (simp add: prod_emb_def)
    have "emeasure (distr (distributions H) (Pi\<^sub>M J (\<lambda>_. M')) (\<lambda>f. restrict f J)) S =
          emeasure (distributions H) (prod_emb H (\<lambda>_. M') J S)"
        apply (rule emeasure_distr_restrict)
      by (simp_all add: "*" sets_distributions in_sets)
    also have "... = emeasure (distributions J) S"
      unfolding distributions_def
      apply (subst prod_emb_distr)
      apply (subst prod.emeasure_prod_emb)
      using distributions_def in_sets sets_distributions * by presburger+
    finally show "emeasure (distributions J) S 
                = emeasure (distr (distributions H) (Pi\<^sub>M J (\<lambda>_. M')) (\<lambda>f. restrict f J)) S"
      by argo
  qed
qed (rule prob_space_distributions)


locale polish_stochastic = stochastic_process M "borel :: 'b::polish_space measure" I X
  for M and I and X

sublocale polish_stochastic \<subseteq> polish_projective I distributions
  by (simp add: polish_projective.intro projective_family_axioms)

lemma distributed_cong_random_variable:
  assumes "M = K" "N = L" "AE x in M. X x = Y x" "X \<in> M \<rightarrow>\<^sub>M N" "Y \<in> K \<rightarrow>\<^sub>M L" "f \<in> borel_measurable N"
  shows "distributed M N X f \<longleftrightarrow> distributed K L Y f"
  using assms by (auto simp add: distributed_def distr_cong_AE)

lemma (in prob_space) indep_sets_indep_set:
  assumes "indep_sets F I" "i \<in> I" "j \<in> I" "i \<noteq> j"
  shows "indep_set (F i) (F j)"
  unfolding indep_set_def
proof (rule indep_setsI)
  show "(case x of True \<Rightarrow> F i | False \<Rightarrow> F j) \<subseteq> events" for x
    using assms by (auto split: bool.split simp: indep_sets_def)
  fix A J assume *: "J \<noteq> {}" "J \<subseteq> UNIV" "\<forall>ja\<in>J. A ja \<in> (case ja of True \<Rightarrow> F i | False \<Rightarrow> F j)"
  {
    assume "J = UNIV"
    then have "indep_sets F I" "{i,j} \<subseteq> I" "{i, j} \<noteq> {}" "finite {i,j}" "\<forall>x \<in> {i,j}. (\<lambda>x. if x = i then A True else A False) x \<in> F x"
      using * assms apply simp_all
      by (simp add: bool.split_sel)
    then have "prob (\<Inter>j\<in>{i, j}. if j = i then A True else A False) = (\<Prod>j\<in>{i, j}. prob (if j = i then A True else A False))"
      by (rule indep_setsD)
    then have "prob (A True \<inter> A False) = prob (A True) * prob (A False)"
      using assms by (auto simp: ac_simps)
  } note X = this
  consider "J = {True, False}" | "J = {False}" | "J = {True}"
    using *(1,2) unfolding UNIV_bool by blast
  then show "prob (\<Inter> (A ` J)) = (\<Prod>j\<in>J. prob (A j))"
    using X by (cases; auto)
qed

lemma (in prob_space) indep_vars_indep_var:
  assumes "indep_vars M' X I" "i \<in> I" "j \<in> I" "i \<noteq> j"
  shows "indep_var (M' i) (X i) (M' j) (X j)"
  using assms unfolding indep_vars_def indep_var_eq
  by (meson indep_sets_indep_set)

text \<open> For all sorted lists of indices, the increments specified by this list are independent \<close>

definition (in prob_space) "indep_increments M' X I \<longleftrightarrow>
  (\<forall>l. set l \<subseteq> I \<and> sorted l \<and> length l \<ge> 2 \<longrightarrow>
     indep_vars (\<lambda>_. M') (\<lambda>k v. X (l!k) v - X (l!(k-1)) v) {1..<length l})"

lemma (in prob_space) indep_incrementsE:
  assumes "indep_increments M' X I"
      and "set l \<subseteq> I \<and> sorted l \<and> length l \<ge> 2"
    shows "indep_vars (\<lambda>_. M') (\<lambda>k v. X (l!k) v - X (l!(k-1)) v) {1..<length l}"
  using assms unfolding indep_increments_def by blast

lemma (in prob_space) indep_incrementsI:
  assumes "\<And>l. set l \<subseteq> I \<Longrightarrow> sorted l \<Longrightarrow> length l \<ge> 2 \<Longrightarrow>
   indep_vars (\<lambda>_. M') (\<lambda>k v. X (l!k) v - X (l!(k-1)) v) {1..<length l}"
  shows "indep_increments M' X I"
  unfolding indep_increments_def using assms by blast

lemma (in prob_space) indep_increments_indep_var:
  assumes "indep_increments M' X I" "h \<in> I" "j \<in> I" "k \<in> I" "h \<le> j" "j \<le> k"
  shows "indep_var M' (\<lambda>v. X j v - X h v) M' (\<lambda>v. X k v - X j v)"
proof -
  let ?l = "[h,j,k]"
  have l: "set ?l \<subseteq> I \<and> sorted ?l \<and> 2 \<le> length ?l"
    using assms by auto
  have 1: "indep_vars (\<lambda>_. M') (\<lambda>k v. X (?l!k) v - X (?l!(k-1)) v) {1..<length ?l}"
    by (fact indep_incrementsE[OF assms(1) l])
  have 2: "1 \<in> {1..<length ?l}"
    by simp
  have 3: "2 \<in> {1..<length ?l}"
    by simp
  have 4: "(1 :: nat) \<noteq> 2"
    by simp
  from indep_vars_indep_var[OF 1 2 3 4] show "indep_var M' (\<lambda>v. X j v - X h v) M' (\<lambda>v. X k v - X j v)"
    by simp
qed

definition (in prob_space) "stationary_increments M' X \<longleftrightarrow>
(\<forall>t1 t2 k. t1 > 0 \<and> t2 > 0 \<and> k > 0 \<longrightarrow> 
     distr M M' (\<lambda>v. X (t1 + k) v - X t1 v) = distr M M' (\<lambda>v. X (t2 + k) v - X t2 v))"

locale wiener = prob_space +
  fixes W :: "real \<Rightarrow> 'a \<Rightarrow> real"
  assumes stochastic_process: "polish_stochastic M W"
      and init_0[simp]: "W 0 x = 0" (* removed probability 1 *)
      and indep_increments: "indep_increments borel W {0..}"
      and normal_increments: "\<And>s t. 0 \<le> s \<and> s < t \<Longrightarrow> distributed M lborel (\<lambda>v. W t v - W s v) (normal_density 0 (sqrt (t-s)))"

sublocale wiener \<subseteq> stochastic_process M borel "{0..}" W
  using polish_stochastic_def stochastic_process by blast

sublocale wiener \<subseteq> polish_projective "{0..}" distributions
  by (simp add: polish_projective.intro projective_family_axioms)

context wiener
begin

lemma stationary_Wiener: "stationary_increments lborel W"
  unfolding stationary_increments_def
proof auto
  fix t1 t2 k :: real
  assume "t1 > 0" "t2 > 0" "k > 0"
  then have "distributed M lborel (\<lambda>v. W (t1 + k) v - W t1 v) (normal_density 0 (sqrt k))"
    using normal_increments[of "t1" "t1 + k"] by simp
  moreover have "distributed M lborel (\<lambda>v. W (t2 + k) v - W t2 v) (normal_density 0 (sqrt k))"
    using normal_increments[of "t2" "t2 + k"] \<open>0 < k\<close> \<open>0 < t2\<close> by simp
  ultimately show "distr M lborel (\<lambda>v. W (t1 + k) v - W t1 v) = distr M lborel (\<lambda>v. W (t2 + k) v - W t2 v)"
    unfolding distributed_def by argo
qed

lemma indep_var_Wiener:
  assumes "0 \<le> s" "s \<le> t"
  shows "indep_var borel (W s) borel (\<lambda>x. W t x - W s x)"
proof -
  have "indep_var borel (\<lambda>x. W s x - W 0 x) borel (\<lambda>x. W t x - W s x)"
    using assms indep_increments indep_increments_indep_var by fastforce
  then show ?thesis
    by simp
qed

lemma Wiener_distributed_t: "t > 0 \<Longrightarrow> distributed M lborel (W t) (normal_density 0 (sqrt t))"
proof -
  assume "t > 0"
  then have 1: "distributed M lborel (\<lambda>v. W t v - W 0 v) (normal_density 0 (sqrt t))"
    using normal_increments[of 0 t] by simp
  have "AE x in M. (\<lambda>v. W t v - W 0 v) x = W t x"
    using init_0 AE_prob_1 by force
  then have "distr M lborel (\<lambda>v. W t v - W 0 v) = distr M lborel (W t)"
    by (intro distr_cong_AE; simp)
  then show "distributed M lborel (W t) (normal_density 0 (sqrt t))"
    using 1 unfolding distributed_def by simp
qed

lemma Wiener_expectation: "t \<ge> 0 \<Longrightarrow> expectation (W t) = 0"
proof -
  have exp_0: "expectation (W 0) = 0"
    by (simp add: integral_eq_zero_AE)
  moreover {
    assume *: "t > 0"
    then have "distributed M lborel (W t) (normal_density 0 (sqrt t))"
      by (rule Wiener_distributed_t)
    then have "expectation (W t) = 0"
      using "*" normal_distributed_expectation real_sqrt_gt_0_iff by blast
  }
  ultimately show "t \<ge> 0 \<Longrightarrow> expectation (W t) = 0"
    by fastforce
qed

lemma Wiener_variance:"t \<ge> 0 \<Longrightarrow> variance (W t) = t"
proof -
  have "variance (W 0) = 0"
    by (simp add: integral_eq_zero_AE)
  moreover {
    assume "t > 0"
    then have "sqrt t > 0"
      by simp
    then have "variance (W t) = sqrt t ^ 2"
      using normal_distributed_variance \<open>0 < t\<close> Wiener_distributed_t by blast
    also have "... = t"
      using \<open>0 < t\<close> by auto
    finally have ?thesis .
  }
  ultimately show "t \<ge> 0 \<Longrightarrow> variance (W t) = t"
    by (cases "t > 0"; auto)
qed

theorem integrable_W: "t \<ge> 0 \<Longrightarrow> integrable M (W t)"
proof -
  have "has_bochner_integral M (W 0) 0"
    by (simp add: has_bochner_integral_cong has_bochner_integral_zero)
  then have "integrable M (W 0)"
    using integrable.simps by blast
  moreover {
    assume *: "t > 0"
    then have "distributed M lborel (W t) (normal_density 0 (sqrt t))"
      by (fact Wiener_distributed_t)
    then have ?thesis
      by (simp add: "*" distributed_integrable_var integrable_normal_moment_nz_1)
  }
  ultimately show "t \<ge> 0 \<Longrightarrow> integrable M (W t)"
    by fastforce
qed

lemma integrable_W_squared: "t \<ge> 0 \<Longrightarrow> integrable M (\<lambda>x. (W t x)\<^sup>2)"
proof -
  have "has_bochner_integral M (\<lambda>x. (W 0 x)\<^sup>2) 0"
    by (simp add: has_bochner_integral_zero)
  moreover {
    assume "t > 0"
    then have "sqrt t > 0"
      by simp
    then have "integrable lborel (\<lambda>x. normal_density 0 (sqrt t) x * x\<^sup>2)"
      using integrable_normal_moment[of "sqrt t" 0 2] by simp
    then have ?thesis
      apply (subst distributed_integrable[where g="\<lambda>x. x\<^sup>2" and N = lborel and f="normal_density 0 (sqrt t)", symmetric])
      using Wiener_distributed_t \<open>0 < t\<close> apply blast
      by auto
  }
  ultimately show "t \<ge> 0 \<Longrightarrow> ?thesis"
    using integrable.simps less_eq_real_def by blast
qed

lemma Wiener_expectation_prod_le:
  assumes "0 \<le> s" "s \<le> t"
  shows "expectation (\<lambda>x. W s x * W t x) = s"
proof -
  have "indep_var borel (W s) borel (\<lambda>x. W t x - W s x)"
    using assms indep_var_Wiener by blast
  then have "integrable M (\<lambda>x. W s x * (W t x - W s x))"
    using integrable_W assms indep_var_integrable[of "W s" "(\<lambda>x. W t x - W s x)"] by auto
  moreover have "integrable M (\<lambda>x. (W s x)\<^sup>2)"
    by (simp add: assms(1) integrable_W_squared)
  moreover have "(\<lambda>x. W s x * W t x) = (\<lambda>x. W s x * (W t x - W s x) + W s x ^ 2)"
    by (simp add: fun_eq_iff power2_eq_square right_diff_distrib)
  ultimately have "expectation (\<lambda>x. W s x * W t x) = expectation (\<lambda>x. W s x * (W t x - W s x)) + expectation (\<lambda>x. W s x ^ 2)"
    by simp
  also have "... = expectation (W s) * expectation (\<lambda>x. W t x - W s x) + expectation (\<lambda>x. W s x ^ 2)"
    using indep_var_Wiener[OF assms] indep_var_lebesgue_integral apply auto
    using assms indep_var_lebesgue_integral wiener.integrable_W wiener_axioms by fastforce
  also have "... = expectation (\<lambda>x. W s x ^ 2)"
    using Wiener_expectation assms(1) by simp
  also have "... = s"
    using Wiener_variance
    by (simp add: Wiener_variance Wiener_expectation assms(1))
  finally show ?thesis .
qed

corollary Wiener_expectation_prod: 
  assumes "s \<ge> 0" "t \<ge> 0"
  shows "expectation (\<lambda>x. W s x * W t x) = min s t"
  apply (cases "s \<le> t")
    apply (simp add: Wiener_expectation_prod_le assms(1))
    apply (subst mult.commute, simp add: Wiener_expectation_prod_le assms(2))
  done

lemma Wiener_distributions_emeasure:
  assumes "J \<subseteq> {0..}" "finite J" "X \<in> sets (\<Pi>\<^sub>M i\<in>J. borel)"
  shows "distributions J X = undefined"

lemma Wiener_lim:
  assumes "J \<subseteq> {0..}" "finite J" "X \<in> sets (\<Pi>\<^sub>M i\<in>J. borel)"
  shows "lim (emb {0..} J X) = distributions J X"
  using assms emeasure_lim_emb by presburger

lemma Wiener_PiM_density: (* distribution given by 37.6 in Billingsley *)
  assumes "sorted ls" "length ls \<ge> 2" "set ls \<subseteq> {0..}"
  shows "distributed M lborel (W t) (normal_density 0 (sqrt t))"
  oops
end

theorem (in prob_space) Wiener_scale_invariant:
  assumes "wiener M W"
  shows "stochastic_process.distributions M borel W = 
        stochastic_process.distributions M borel (\<lambda>t x. 1/(sqrt c) * W (c*t) x)"n 
  oops

end