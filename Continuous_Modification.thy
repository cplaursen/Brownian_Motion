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
     apply auto[1]
    apply (rule borel_measurable_mono_on_fnc[OF mono])
    done
  then have "{x \<in> space M. f (abs (X x)) \<ge> f \<epsilon>} \<in> sets M"
    by measurable
  then have "f \<epsilon> * emeasure M {p \<in> space M. abs (X p) \<ge> \<epsilon>} \<le> integral\<^sup>N M (\<lambda>x. ennreal (f \<epsilon>) * indicator {x \<in> space M. f (abs (X x)) \<ge> f \<epsilon>} x)"
    apply (simp add: nn_integral_cmult_indicator)
    apply (rule mult_left_mono)
     apply (rule emeasure_mono)
    apply simp_all
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

lemma suminf_shift:
  assumes "summable (f :: nat \<Rightarrow> 'a :: {t2_space, topological_group_add, comm_monoid_add})"
  shows "(\<Sum>n. f n) = f 0 + (\<Sum>n. f (Suc n))"
proof -
  obtain s where s: "s = suminf f"
    using assms summable_def by blast
  then have "(\<lambda>n. \<Sum>i\<le>n. f i) \<longlonglongrightarrow> s"
    using summable_LIMSEQ'[OF assms] by argo
  then have "(\<lambda>n. f 0 + (\<Sum>i<n. f (Suc i))) \<longlonglongrightarrow> s"
    by (simp add: sum.atMost_shift)
  then have "(\<lambda>n. f 0 +  (\<Sum>i<n. f (Suc i)) - f 0) \<longlonglongrightarrow> (s - f 0)"
    using tendsto_diff by blast
  moreover have "(\<lambda>n. f 0 +  (\<Sum>i<n. f (Suc i)) - f 0) = (\<lambda>n. (\<Sum>i<n. f (Suc i)))"
    by (metis add.commute add_diff_cancel)
  ultimately have "(\<lambda>n. \<Sum>i<n. f (Suc i)) \<longlonglongrightarrow> (s - f 0)"
    by argo
  then have *: "(\<Sum>n. f (Suc n)) = (s - f 0)"
    using sums_def sums_iff by blast
  then show ?thesis
    by (metis s add.commute diff_add_cancel)
qed

lemma Max_finite_image_ex:
  assumes "finite S" "S \<noteq> {}" "P (MAX k\<in>S. f k)" 
  shows "\<exists>k \<in> S. P (f k)"
  by (metis (mono_tags, opaque_lifting) assms Max_in empty_is_image finite_imageI image_iff)

text \<open> Klenke 21.6 - Kolmorogov-Chentsov\<close>

theorem holder_continuous_modification:
  fixes X :: "(real, 'a, real) stochastic_process"
  assumes index: "proc_index X = {0..}"
      and real_valued[measurable]: "proc_target X = borel"
      and gt_0: "a > 0" "b > 0" "C > 0"
      and integrable_X: "\<And>s t. t \<ge> 0 \<Longrightarrow> integrable (proc_source X) (X t)"
      and expectation: "\<And>s t.\<lbrakk>s \<ge> 0; t \<ge> 0\<rbrakk> \<Longrightarrow> 
          (\<integral>\<^sup>+ x. \<bar>X t x - X s x\<bar> powr a \<partial>proc_source X) \<le> C * (dist t s) powr (1+b)"
    shows "\<exists>Y. modification X Y \<and> (\<forall>\<gamma>\<in>{0<..<(b / a)}. AE x in proc_source Y. local_holder_on \<gamma> {0..} (\<lambda>t. Y t x))"
proof -
  let ?M = "proc_source X"
  { fix s t \<epsilon> :: real assume *: "s \<ge> 0" "t \<ge> 0" "\<epsilon> > 0"
    let ?inc = "\<lambda>x. \<bar>X t x - X s x\<bar> powr a"
    have "emeasure ?M {x \<in> space ?M. \<epsilon> \<le> \<bar>X t x - X s x\<bar>}
     \<le> integral\<^sup>N ?M ?inc / \<epsilon> powr a"
      apply (rule nn_integral_Markov_inequality')
      using *(1,2) borel_measurable_diff integrable_X apply blast
      using gt_0(1) *(3) powr_mono2 by (auto intro: mono_onI)
    also have "... \<le> (C * dist t s powr (1 + b)) / ennreal (\<epsilon> powr a)"
      apply (rule divide_right_mono_ennreal)
      using expectation[OF *(1,2)] ennreal_leI by presburger
    finally have "emeasure ?M {x \<in> space ?M. \<epsilon> \<le> \<bar>process X t x - process X s x\<bar>}
       \<le> (C * dist t s powr (1 + b)) / \<epsilon> powr a"
      using *(3) divide_ennreal gt_0(3) by simp
    then have "\<P>(x in ?M. \<epsilon> \<le> \<bar>process X t x - process X s x\<bar>) \<le> (C * dist t s powr (1 + b)) / \<epsilon> powr a"
      by (smt (verit, del_insts) divide_nonneg_nonneg ennreal_le_iff gt_0(3) mult_nonneg_nonneg powr_ge_pzero proc_source.emeasure_eq_measure)
    (* FROM THIS X s \<rightarrow> X t as s \<rightarrow> t in probability *)
  } note markov = this
  {
    fix n k \<gamma> :: real
    assume gamma: "\<gamma> > 0"
       and k: "k \<ge> 1"
       and n: "n \<ge> 0"
    have "\<P>(x in ?M. 2 powr (- \<gamma> * n) \<le> \<bar>X ((k - 1) * 2 powr - n) x - X (k * 2 powr - n) x\<bar>) \<le> C * 2 powr (-n * (1+b-a*\<gamma>))"
    proof -
      have "\<P>(x in ?M. 2 powr (- \<gamma> * n) \<le> \<bar>X ((k - 1) * 2 powr - n) x - X (k * 2 powr - n) x\<bar>)
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
  } note incr = this
    
  text \<open> In the textbook, we define the following:
  A_n(\<gamma>) = {x. max {\<bar>X ((k - 1) * 2 powr - n) x - X (k * 2 powr - n) x\<bar>, k \<in> {0..2^n}} \<ge> 2 powr -\<gamma> * n}
  B_n = \<Union>m\<ge>n. A_m
  N = limsup (n -> \<infinity>) A_n = \<Inter>n. B_n
  
  We then go on to prove that N is a null set. \<close>
  {
    fix T :: real assume "T > 0"
    fix \<gamma> :: real assume "\<gamma> > 0"
    define A where "A \<equiv> \<lambda>n. {x \<in> space ?M. Max {\<bar>X (real_of_int (k - 1) * 2 powr - real n) x - X (real_of_int k * 2 powr - real n) x\<bar> | k. k \<in> {1..\<lfloor>2^n * T\<rfloor>}} \<ge> 2 powr (-\<gamma> * real n)}"
    let ?B = "\<lambda>n. (\<Union>m\<in>{n..}. A m)"
    let ?N = "\<Inter>n \<in> {1..}. ?B n"
    have A_measurable[measurable]: "A n \<in> sets ?M" for n
      unfolding A_def apply measurable
      by (metis random_X real_valued)+
    {
      fix n assume "2^n * T \<ge> 1"
      then have nonempty: "{1..\<lfloor>2^n * T\<rfloor>} \<noteq> {}"
        by fastforce
    
      have finite: "finite {1..\<lfloor>2^n * T\<rfloor>}"
        by simp
      have "emeasure ?M (A n) \<le> emeasure ?M (\<Union>k \<in> {1..\<lfloor>2^n * T\<rfloor>}.
      {x\<in>space ?M. \<bar>X (real_of_int (k - 1) * 2 powr - real n) x - X (real_of_int k * 2 powr - real n) x\<bar> \<ge> 2 powr (- \<gamma> * real n)})"
      (is "emeasure ?M (A n) \<le> emeasure ?M ?R")
      proof (rule emeasure_mono, intro subsetI)
        fix x assume *: "x \<in> A n"
        from * have in_space: "x \<in> space ?M"
          unfolding A_def by fast
        from * have "2 powr (- \<gamma> * real n) \<le> Max {\<bar>X (real_of_int (k - 1) * 2 powr - real n) x - X (real_of_int k * 2 powr - real n) x\<bar> |k. k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}}"
          unfolding A_def by blast
        then have "\<exists>k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}. 2 powr (- \<gamma> * real n) \<le> \<bar>X (real_of_int (k - 1) * 2 powr - real n) x - X (real_of_int k * 2 powr - real n) x\<bar>"
          apply (simp only: setcompr_eq_image)
          apply (rule Max_finite_image_ex[where P="\<lambda>x. 2 powr (- \<gamma> * real n) \<le> x", OF finite nonempty])
          apply (metis Collect_mem_eq)
          done
        then show "x \<in> ?R"
          using in_space by simp
      next
        show "?R \<in> sets ?M"
          apply measurable
          by (smt (verit) real_valued random_X)+
      qed
      also have "... \<le> (\<Sum>k\<in>{1..\<lfloor>2^n * T\<rfloor>}. emeasure ?M 
    {x\<in>space ?M. \<bar>X (real_of_int (k - 1) * 2 powr - real n) x - X (real_of_int k * 2 powr - real n) x\<bar> \<ge> 2 powr (- \<gamma> * real n)})"
        apply (rule emeasure_subadditive_finite)
         apply blast
        apply (subst image_subset_iff)
        apply (intro ballI)
        apply measurable
         apply (metis random_X real_valued)+
        done
      also have "... \<le> C * 2 powr (- n * (1 + b - a * \<gamma>)) * (card {1..\<lfloor>2 ^ n * T\<rfloor>})"
      proof -
        {
          fix k assume "k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}"
          then have "real_of_int k \<ge> 1"
            by presburger
          have "measure ?M {x \<in> space ?M. 2 powr (- \<gamma> * real n) \<le> \<bar>X (real_of_int (k - 1) * 2 powr - real n) x - X (real_of_int k * 2 powr - real n) x\<bar>} \<le> C * 2 powr (-(real n) * (1+b-a*\<gamma>))"
            using incr[OF \<open>\<gamma> > 0\<close> \<open>real_of_int k \<ge> 1\<close>] by simp
        } note X = this
        then have "sum (\<lambda>k. measure ?M {x \<in> space ?M. 2 powr (- \<gamma> * real n) \<le> \<bar>X (real_of_int (k - 1) * 2 powr - real n) x - X (real_of_int k * 2 powr - real n) x\<bar>}) {1..\<lfloor>2 ^ n * T\<rfloor>} \<le> of_nat (card {1..\<lfloor>2 ^ n * T\<rfloor>}) * (C * 2 powr (-(real n) * (1+b-a*\<gamma>)))"
          by (rule sum_bounded_above)
        then show ?thesis
          apply (subst proc_source.emeasure_eq_measure)
          apply (subst sum_ennreal)
          apply auto
          apply (rule ennreal_leI)
          apply argo
          done
        qed
      also have "... = C * 2 powr (- n * (1 + b - a * \<gamma>)) * \<lfloor>2 ^ n * T\<rfloor>"
        using \<open>0 < T\<close> by force
      finally have "emeasure ?M (A n) \<le> C * 2 powr (- n * (1 + b - a * \<gamma>)) * \<lfloor>2 ^ n * T\<rfloor>".
    } note A = this
    thm suminf_def
    have "emeasure ?M (?B n) \<le> (\<Sum>m. emeasure ?M (A (m + n)))" for n
    proof (induct n)
      case 0
      show ?case
        apply simp
        apply (rule emeasure_subadditive_countably)
      apply (intro subsetI)
      using A_measurable by auto
    next
      case (Suc n)
      have "(\<Sum>m. measure ?M (A (m + n))) = measure ?M (A n) + (\<Sum>m. measure ?M (A (m + (Suc n))))"
        apply (subst suminf_shift)
         apply auto
        sorry
      have "{n..} = insert n {Suc n ..}"
        by (simp add: atLeast_Suc insert_absorb)
      then have "\<Union> (A ` {n..}) = A n \<union> (\<Union> (A ` {Suc n..}))"
        apply (subst Union_image_insert[symmetric])
        by presburger
      then have "emeasure ?M (\<Union> (A ` {n..})) \<le> emeasure ?M (A n) + emeasure ?M (\<Union> (A ` {Suc n..}))"
        apply simp
        by (meson A_measurable emeasure_subadditive image_subset_iff sets.countable_UN)
      also have "... \<le> undefined"
        sorry
      then show ?case sorry
    qed
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