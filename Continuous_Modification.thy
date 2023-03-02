theory Continuous_Modification
  imports Stochastic_Process Holder_Continuous
begin

text \<open> Klenke 5.11: Markov inequality. Compare with @{thm nn_integral_Markov_inequality} \<close>

lemma nn_integral_Markov_inequality':
  fixes f :: "real \<Rightarrow> real" and \<epsilon> :: real
  assumes X[measurable]: "X \<in> borel_measurable M"
      and mono: "mono_on {0..} f"
      and e: "\<epsilon> > 0" "f \<epsilon> > 0"
    shows "emeasure M {p \<in> space M. abs (X p) \<ge> \<epsilon>} \<le> integral\<^sup>N M (\<lambda>x. f (abs (X x))) / f \<epsilon>"
proof -
  have "(\<lambda>x. f (abs (X x))) \<in> borel_measurable M"
    apply (rule measurable_compose[of "\<lambda>x. abs (X x)" M "restrict_space borel {0..}"])
     apply (subst measurable_restrict_space2_iff)
     apply auto
    apply (rule borel_measurable_mono_on_fnc[OF mono])
    done
  then have "{x \<in> space M. f (abs (X x)) \<ge> f \<epsilon>} \<in> sets M"
    by measurable
  then have "f \<epsilon> * emeasure M {p \<in> space M. abs (X p) \<ge> \<epsilon>} \<le> integral\<^sup>N M (\<lambda>x. ennreal (f \<epsilon>) * indicator {x \<in> space M. f (abs (X x)) \<ge> f \<epsilon>} x)"
    apply (simp add: nn_integral_cmult_indicator)
    apply (rule mult_left_mono)
     apply (rule emeasure_mono)
      apply auto
    using e mono_onD[OF mono] apply fastforce
    done
  also have "... \<le> integral\<^sup>N M (\<lambda>x. ennreal (f (abs (X x))) * indicator {x \<in> space M. f (abs (X x)) \<ge> f \<epsilon>} x)"
    apply (rule nn_integral_mono)
    subgoal for x
      apply (cases "f \<epsilon> \<le> f \<bar>X x\<bar>")
      using ennreal_leI by auto
    done
  also have "... \<le> integral\<^sup>N M (\<lambda>x. f (abs (X x)))"
    by (simp add:divide_right_mono_ennreal nn_integral_mono indicator_def)
  finally show ?thesis
  proof -
    assume "(f \<epsilon>) * emeasure M {p \<in> space M. \<epsilon> \<le> \<bar>X p\<bar>} \<le> \<integral>\<^sup>+ x. (f \<bar>X x\<bar>) \<partial>M"
    then have 1: "((f \<epsilon>) * emeasure M {p \<in> space M. \<epsilon> \<le> \<bar>X p\<bar>}) / f \<epsilon> \<le> (\<integral>\<^sup>+ x. (f \<bar>X x\<bar>) \<partial>M) / f \<epsilon>"
      by (fact divide_right_mono_ennreal)
    have "((f \<epsilon>) * emeasure M {p \<in> space M. \<epsilon> \<le> \<bar>X p\<bar>}) / f \<epsilon> = (f \<epsilon>) * (inverse (ennreal (f \<epsilon>))) * emeasure M {p \<in> space M. \<epsilon> \<le> \<bar>X p\<bar>}"
      using ennreal_divide_times divide_ennreal_def mult.assoc by force
    also have "... = 1 * emeasure M {p \<in> space M. \<epsilon> \<le> \<bar>X p\<bar>}"
      using divide_ennreal divide_ennreal_def e(2) by force
    also have "... = emeasure M {p \<in> space M. \<epsilon> \<le> \<bar>X p\<bar>}"
      by auto
    finally show ?thesis
      using 1 by presburger
  qed
qed

text \<open> Klenke 21.6 - Kolmorogov-Chentsov\<close>

theorem holder_continuous_modification:
  fixes X :: "(real, 'a, real) stochastic_process"
  assumes index: "proc_index X = {0..}"
      and gt_0: "a > 0" "b > 0" "C > 0"
      and integrable_X: "\<And>s t. t \<ge> 0 \<Longrightarrow> integrable (proc_source X) (X t)"
      and integrable_interval: "\<And>s t.\<lbrakk>s \<ge> 0; t \<ge> 0\<rbrakk> \<Longrightarrow> integrable (proc_source X) (\<lambda>x. \<bar>X t x - X s x\<bar> powr a)"
      and expectation: "\<And>s t.\<lbrakk>s \<ge> 0; t \<ge> 0\<rbrakk> \<Longrightarrow> 
          prob_space.expectation (proc_source X) (\<lambda>x. \<bar>X t x - X s x\<bar> powr a) \<le> C * (dist t s) powr (1+b)"
    shows "\<exists>Y. modification X Y \<and> (\<forall>\<gamma>\<in>{0<..<(b / a)}. AE x in proc_source Y. local_holder_on \<gamma> {0..} (\<lambda>t. Y t x))"
proof -
  let ?M = "proc_source X"
  interpret p: prob_space "?M"
    by (simp add: proc_source.prob_space_axioms)
  { fix s t \<epsilon> :: real assume *: "s \<ge> 0" "t \<ge> 0" "\<epsilon> > 0"
    let ?inc = "\<lambda>x. \<bar>X t x - X s x\<bar> powr a"
    have "emeasure (proc_source X) {x \<in> space (proc_source X). \<epsilon> \<le> \<bar>X t x - X s x\<bar>}
     \<le> integral\<^sup>N (proc_source X) ?inc / \<epsilon> powr a"
      apply (rule nn_integral_Markov_inequality')
      using *(1,2) borel_measurable_diff integrable_X apply blast
      using gt_0(1) *(3) powr_mono2 by (auto intro: mono_onI)
    also have "... = prob_space.expectation (proc_source X) ?inc / ennreal (\<epsilon> powr a)"
      apply (rule arg_cong[where f= "\<lambda>x. x / ennreal (\<epsilon> powr a)"])
      apply (rule nn_integral_eq_integral)
      using integrable_interval[OF *(1,2)] apply auto
      done
    also have "... \<le> (C * dist t s powr (1 + b)) / ennreal (\<epsilon> powr a)"
      apply (rule divide_right_mono_ennreal)
      using expectation[OF *(1,2)] ennreal_leI by presburger
    finally have "emeasure (proc_source X) {x \<in> space (proc_source X). \<epsilon> \<le> \<bar>process X t x - process X s x\<bar>}
       \<le> (C * dist t s powr (1 + b)) / \<epsilon> powr a"
      using *(3) divide_ennreal gt_0(3) by simp
    then have "\<P>(x in proc_source X. \<epsilon> \<le> \<bar>process X t x - process X s x\<bar>) \<le> (C * dist t s powr (1 + b)) / \<epsilon> powr a"
      by (smt (verit, del_insts) divide_nonneg_nonneg ennreal_le_iff gt_0(3) mult_nonneg_nonneg powr_ge_pzero proc_source.emeasure_eq_measure)
    (* FROM THIS X s \<rightarrow> X t as s \<rightarrow> t in probability *)
  } note markov = this
  thm CollectI
  define dyadic_n :: "nat \<Rightarrow> real set" where "dyadic_n \<equiv> \<lambda>n. {of_nat k / (2 ^ n) | k. True}"
  have "dyadics = (\<Union>n. dyadic_n n)"
    unfolding dyadics_def dyadic_n_def by auto
  {
    fix n k \<gamma> :: real
    assume gamma: "\<gamma> > 0 \<and> \<gamma> \<le> 1"
       and k: "k > 1"
       and n: "n > 0"
    have "\<P>(x in proc_source X. 2 powr (- \<gamma> * n) \<le> \<bar>X ((k - 1) * 2 powr - n) x - X (k * 2 powr - n) x\<bar>) \<le> C * 2 powr (-n * (1+b-a*\<gamma>))"
    proof -
      have "\<P>(x in proc_source X. 2 powr (- \<gamma> * n) \<le> \<bar>X ((k - 1) * 2 powr - n) x - X (k * 2 powr - n) x\<bar>)
           \<le> C * dist ((k - 1) * 2 powr - n) (k * 2 powr - n) powr (1 + b) / (2 powr (- \<gamma> * n)) powr a"
        apply (rule markov)
        using k by auto
      also have "... = C * 2 powr (- n - b * n) / 2 powr (- \<gamma> * n * a)"
        by (auto simp: dist_real_def n k gamma powr_powr field_simps)
      also have "... =  C * 2 powr (-n * (1+b-a*\<gamma>))"
        apply (auto simp: field_simps)
        by (smt (verit) powr_add)
      finally show ?thesis .
    qed
    let ?A = "\<lambda>n \<gamma>. {x. Sup {\<bar>X ((k - 1) * 2 powr - n) x - X (k * 2 powr - n) x\<bar> } \<ge> 2 powr (-\<gamma> * n)}"
      \<comment> \<open> Klenke restricts k \<in> {1..2^n}, this works for interval {0..1}\<close>
  }
  then show "\<exists>Y. modification X Y \<and> (\<forall>\<gamma>\<in>{0<..<(b / a)}. AE x in proc_source Y. local_holder_on \<gamma> {0..} (\<lambda>t. Y t x))"
    sorry
qed

(* Proof sketch that we can extend a modification on {0..T} to {0..}
  {
    have *: "\<And>T. T > 0 \<Longrightarrow> \<exists>Y. modification (restrict_index X {0..T}) Y \<and> (\<forall>\<gamma>\<in>{0<..<(b / a)}.
               AE x in proc_source Y. local_holder_on \<gamma> {0..T} (\<lambda>t. Y t x))"
      sorry (* should follow from holder_continuous_modification_finite *)
    fix S T ::real assume ST: "S > 0" "T > 0"
    obtain P where P: "modification (restrict_index X {0..S}) P" "(\<forall>\<gamma>\<in>{0<..<(b / a)}.
               AE x in proc_source P. local_holder_on \<gamma> {0..S} (\<lambda>t. P t x))"
      using *[OF ST(1)] by blast
    obtain Q where Q: "modification (restrict_index X {0..T}) Q" "(\<forall>\<gamma>\<in>{0<..<(b / a)}.
               AE x in proc_source Q. local_holder_on \<gamma> {0..T} (\<lambda>t. Q t x))"
      using *[OF ST(2)] by blast
    have mod_restrict: "modification (restrict_index P {0..min S T}) (restrict_index Q {0..min S T})"
    proof -
      have "modification (restrict_index X {0..min S T}) (restrict_index P {0..min S T})"
        using P(1) restrict_index_override modification_restrict_index by fastforce
      moreover have "modification (restrict_index X {0..min S T}) (restrict_index Q {0..min S T})"
        using Q(1) restrict_index_override modification_restrict_index by fastforce
      ultimately show ?thesis
        using modification_sym modification_trans by blast
    qed
    then have "indistinguishable (restrict_index P {0..min S T}) (restrict_index Q {0..min S T})"
    proof -
      have "b / a > 0"
        using gt_0 by auto
      then obtain \<gamma> where \<gamma>: "\<gamma> \<in> {0<..<(b / a)}" "\<gamma> \<le> 1"
        by (simp, meson field_lbound_gt_zero less_eq_real_def less_numeral_extra(1))
      then have "AE x in proc_source P. continuous_on {0..S} (\<lambda>t. P t x)"
        using P(2) local_holder_continuous by fast
      then have 1: "AE x in proc_source (restrict_index P {0..min S T}). continuous_on {0..min S T} (\<lambda>t. P t x)"
        apply (subst restrict_index_source)
        using continuous_on_subset by fastforce
      have "AE x in proc_source Q. continuous_on {0..T} (\<lambda>t. Q t x)"
        using Q(2) \<gamma> local_holder_continuous by fast
      then have 2: "AE x in proc_source (restrict_index Q {0..min S T}). continuous_on {0..min S T} (\<lambda>t. Q t x)"
        apply (subst restrict_index_source)
        using continuous_on_subset by fastforce
      show ?thesis
        apply (rule modification_continuous_indistinguishable)
           apply (fact mod_restrict)
        using ST(1) ST(2) apply force
        using 1 apply fastforce 
        using 2 apply fastforce
        done
    qed
    then have "\<exists>N \<in> null_sets (proc_source P).
   {\<omega>. \<exists>t \<in> {0..min S T}.(restrict_index P {0..min S T}) t \<omega> \<noteq> (restrict_index P {0..min S T}) t \<omega>} \<subseteq> N"
      using indistinguishable_null_ex by blast
    text \<open> We've shown that for any S T > 0, we can produce processes X^T that are modifications restricted
  to min S T. We can then define our final process pointwise as X t = X^T t for all \<omega> in \<Omega>_\<infinity> \<close>
    then have ?thesis
      sorry
  } note X = this
*)

corollary holder_continuous_modification:
  fixes X :: "(real, 'a, real) stochastic_process"
  assumes index: "proc_index X = {0..}"
      and gt_0: "a > 0" "b > 0" "C > 0"
      and expectation: "\<And>s t. \<lbrakk>s \<ge> 0; t \<ge> 0\<rbrakk> \<Longrightarrow> 
          prob_space.expectation (proc_source X) (\<lambda>x. (X t x - X s x) powr a) \<le> C * (dist t s) powr (1+b)"
    shows "\<exists>Y. modification X Y \<and> (\<forall>\<gamma>\<in>{0<..<(b / a)}. AE x in proc_source Y. local_holder_on \<gamma> {0..} (\<lambda>t. Y t x))"
proof -
  let ?M = "proc_source X"
  interpret p: prob_space "?M"
    by (simp add: proc_source.prob_space_axioms)
  text \<open> Quoting Klenke: It is enough to show that for any T > 0 the process X on [0,T] has a
  modification X^T that is locally H{\"o}lder-continuous of any order \<gamma> \<in> (0, b/a).
  For S, T > 0, by lemma 21.5, two such modifications X^S and X^T are indistinguishable on
  [0, min S T], hence
  \[\<Omega>_{S, T} := {\<omega>. \<exists>t \<in> {0..min S T}. X^T t \<omega> \<noteq> X^S t \<omega>}\]
  is a null set and thus also \<Omega>_\<infinity> := \<Union>s \<in> (\<nat> \<times> \<nat>). \<Omega> s is a null set. Therefore, definining
  \tilde{X}_t(\<omega>) := X_t^t(\<omega>), t \<ge> 0, for \<omega> \<in> \<Omega> \ \<Omega>_\<infinity>, we get that \tilde{X} is the process
  we are looking for \<close>
  oops

  
  text \<open> The theorem goes as follows:
  We have established some bounds on the expectation of the process. We show that this implies that,
for dyadic rationals, the process is Holder continuous on some set of measure 1. We then extend our
modification to a real interval, using the fact that X_s converges to X_t as s -> t. 

\<close>
end