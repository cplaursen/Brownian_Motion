theory Stochastic_Process
  imports Markov_Semigroup Explorer.Explorer
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

lemma (in prob_space) stochastic_processI:
  assumes "\<And>i. random_variable M' (X i)"
    shows "stochastic_process M M' X"
  by (simp add: assms prob_space_axioms stochastic_process_axioms.intro stochastic_process_def)

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

term return


typedef ('t, 'a, 'b) stochastic_process = "{(M :: 'a measure, M' :: 'b measure, I :: 't set, X :: 't \<Rightarrow> 'a \<Rightarrow> 'b).
   stochastic_process M M' X}"
proof
  show "(return (sigma UNIV {{}, UNIV}) x, sigma UNIV UNIV, UNIV, \<lambda>_ _. c) \<in>
       {(M, M', I, X). stochastic_process M M' X}" for x :: 'a and c :: 'b
    by (simp add: prob_space_return prob_space.stochastic_processI)
qed

definition proc_index :: "('t,'a,'b) stochastic_process \<Rightarrow> 't set" where
"proc_index X = fst (snd (snd (Rep_stochastic_process X)))"

definition proc_source :: "('t,'a,'b) stochastic_process \<Rightarrow> 'a measure" where
"proc_source X = fst (Rep_stochastic_process X)"

definition proc_target :: "('t,'a,'b) stochastic_process \<Rightarrow> 'b measure" where
"proc_target X = fst (snd (Rep_stochastic_process X))"

definition process :: "('t,'a,'b) stochastic_process \<Rightarrow> 't \<Rightarrow> 'a \<Rightarrow> 'b" where
"process X = snd (snd (snd (Rep_stochastic_process X)))"

declare [[coercion process]]

(* Quotient type would make things unnecessarily difficult

definition "on_index_equiv X Y \<equiv> proc_index X = proc_index Y \<and>
  (sets (proc_source X) = sets (proc_source Y)) \<and> (sets (proc_target X) = sets (proc_target Y)) \<and>
  (\<forall>i \<in>proc_index X. process X i = process Y i)"

quotient_type ('t, 'a, 'b) stochastic_process = "('t, 'a, 'b) stochastic_process" / on_index_equiv
  unfolding on_index_equiv_def by (intro equivpI reflpI sympI transpI; simp)
*)

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

definition compatible_processes :: "('t,'a,'b) stochastic_process \<Rightarrow> ('t,'a,'b) stochastic_process \<Rightarrow> bool" where
"compatible_processes X Y \<longleftrightarrow> sets (proc_source X) = sets (proc_source Y) \<and> sets (proc_target X) = sets (proc_target Y)
  \<and> proc_index X = proc_index Y"

definition modification :: "('t,'a,'b) stochastic_process \<Rightarrow> ('t,'a,'b) stochastic_process \<Rightarrow> bool" where
"modification X Y \<longleftrightarrow> compatible_processes X Y \<and> (\<forall>t \<in> proc_index X. AE x in proc_source X. X t x = Y t x)"

lemma modificationI:
  assumes "compatible_processes X Y" "(\<forall>t \<in> proc_index X. AE x in proc_source X. X t x = Y t x)"
  shows "modification X Y"
  unfolding modification_def using assms by blast

definition indistinguishable :: "('t,'a,'b) stochastic_process \<Rightarrow> ('t,'a,'b) stochastic_process \<Rightarrow> bool" where
"indistinguishable X Y \<longleftrightarrow> compatible_processes X Y \<and> (\<exists>N \<in> sets (proc_source X). \<forall>t \<in> proc_index X. {x. X t x \<noteq> Y t x} \<subseteq> N)"

lemma indistinguishableI:
  assumes "compatible_processes X Y" "(\<exists>N \<in> sets (proc_source X). \<forall>t \<in> proc_index X. {x. X t x \<noteq> Y t x} \<subseteq> N)"
  shows "indistinguishable X Y"
  unfolding indistinguishable_def using assms by blast

text \<open> Klenke 21.5 \<close>

lemma
  assumes "modification X Y" "countable (proc_index X)"
  shows "indistinguishable X Y"
  sorry

end