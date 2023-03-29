theory Continuous_Modification
  imports Stochastic_Process Holder_Continuous Dyadic_Interval "Eisbach_Tools.Apply_Trace_Cmd"
begin

text \<open> Klenke 5.11: Markov inequality. Compare with @{thm nn_integral_Markov_inequality} \<close>

lemma nn_integral_Markov_inequality':
  fixes f :: "real \<Rightarrow> real" and \<epsilon> :: real
  assumes X[measurable]: "X \<in> borel_measurable M"
      and mono: "mono_on {0..} f"
      and e: "\<epsilon> > 0" "f \<epsilon> > 0"
    shows "emeasure M {p \<in> space M. abs (X p) \<ge> \<epsilon>} \<le> (\<integral>\<^sup>+ x. f \<bar>X x\<bar> \<partial>M) / f \<epsilon>"
proof -
  have "(\<lambda>x. f (abs (X x))) \<in> borel_measurable M"
    apply (rule measurable_compose[of "\<lambda>x. abs (X x)" M "restrict_space borel {0..}"])
     apply (subst measurable_restrict_space2_iff)
     apply auto[1]
    apply (fact borel_measurable_mono_on_fnc[OF mono])
    done
  then have "{x \<in> space M. f (abs (X x)) \<ge> f \<epsilon>} \<in> sets M"
    by measurable
  then have "f \<epsilon> * emeasure M {p \<in> space M. \<bar>X p\<bar> \<ge> \<epsilon>} \<le> \<integral>\<^sup>+x\<in>{x \<in> space M. f \<epsilon> \<le> f \<bar>X x\<bar>}. f \<epsilon> \<partial>M"
    apply (simp add: nn_integral_cmult_indicator)
    apply (rule mult_left_mono)
     apply (rule emeasure_mono)
    apply simp_all
    using e mono_onD[OF mono] apply fastforce
    done
  also have "... \<le> \<integral>\<^sup>+x\<in>{x \<in> space M. f \<epsilon> \<le> f \<bar>X x\<bar>}. f \<bar>X x\<bar>\<partial>M"
    apply (rule nn_integral_mono)
    subgoal for x
      apply (cases "f \<epsilon> \<le> f \<bar>X x\<bar>")
      using ennreal_leI by auto
    done
  also have "... \<le> \<integral>\<^sup>+ x. f \<bar>X x\<bar> \<partial>M"
    by (simp add: divide_right_mono_ennreal nn_integral_mono indicator_def)
  finally show ?thesis
  proof -
    assume "f \<epsilon> * emeasure M {p \<in> space M. \<epsilon> \<le> \<bar>X p\<bar>} \<le> \<integral>\<^sup>+ x. (f \<bar>X x\<bar>) \<partial>M"
    then have "(f \<epsilon> * emeasure M {p \<in> space M. \<epsilon> \<le> \<bar>X p\<bar>}) / f \<epsilon> \<le> (\<integral>\<^sup>+ x. (f \<bar>X x\<bar>) \<partial>M) / f \<epsilon>"
      by (fact divide_right_mono_ennreal)
    moreover have "(f \<epsilon> * emeasure M {p \<in> space M. \<epsilon> \<le> \<bar>X p\<bar>}) / f \<epsilon> = emeasure M {p \<in> space M. \<epsilon> \<le> \<bar>X p\<bar>}"
    proof -
      have "(f \<epsilon> * emeasure M {p \<in> space M. \<epsilon> \<le> \<bar>X p\<bar>}) / f \<epsilon> = emeasure M {p \<in> space M. \<epsilon> \<le> \<bar>X p\<bar>} * f \<epsilon> / f \<epsilon>"
        by (simp add: field_simps)
      also have "... = emeasure M {p \<in> space M. \<epsilon> \<le> \<bar>X p\<bar>}"
        using e(2) ennreal_mult_divide_eq by force
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by argo
  qed
qed

(* TODO: see if we can reduce the typeclasses of 'a *)
lemma suminf_shift_1:
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

lemma suminf_split:
  assumes "summable (f :: nat \<Rightarrow> 'a :: {t2_space, topological_group_add, comm_monoid_add})"
  shows "(\<Sum>n. f n) = (\<Sum>i<k. f k) + (\<Sum>n. f (n + k))"
  sorry

lemma Max_finite_image_ex:
  assumes "finite S" "S \<noteq> {}" "P (MAX k\<in>S. f k)" 
  shows "\<exists>k \<in> S. P (f k)"
  using bexI[of P "Max (f ` S)" "f ` S"] by (simp add: assms)

lemma measure_leq_emeasure_ennreal: "0 \<le> x \<Longrightarrow> emeasure M A \<le> ennreal x \<Longrightarrow> measure M A \<le> x"
  apply (cases "A \<in> M")
   apply (metis Sigma_Algebra.measure_def enn2real_leI)
   apply (auto simp: measure_notin_sets emeasure_notin_sets)
  done

thm tendsto_at_iff_sequentially

text \<open> Klenke 21.6 - Kolmorogov-Chentsov\<close>

theorem holder_continuous_modification:
  fixes X :: "(real, 'a, real) stochastic_process"
  assumes index: "proc_index X = {0..}"
      and real_valued[measurable]: "proc_target X = borel"
      and gt_0: "a > 0" "b > 0" "C > 0"
      and "b \<le> a" (* Probably follows from other assms *)
      and integrable_X: "\<And>s t. t \<ge> 0 \<Longrightarrow> integrable (proc_source X) (X t)"
      and expectation: "\<And>s t.\<lbrakk>s \<ge> 0; t \<ge> 0\<rbrakk> \<Longrightarrow> 
          (\<integral>\<^sup>+ x. \<bar>X t x - X s x\<bar> powr a \<partial>proc_source X) \<le> C * (dist t s) powr (1+b)"
    shows "\<exists>Y. modification X Y \<and> (\<forall>\<gamma>\<in>{0<..<(b / a)}. \<forall>x \<in> space (proc_source X). local_holder_on \<gamma> {0..} (\<lambda>t. Y t x))"
proof -
  let ?M = "proc_source X"
  {
    text \<open> Here we show that the increments of the stochastic process tend to 0 a.e. as the 
           increment size becomes smaller \<close>
    fix s t \<epsilon> :: real assume *: "s \<ge> 0" "t \<ge> 0" "\<epsilon> > 0"
    let ?inc = "\<lambda>x. \<bar>X t x - X s x\<bar> powr a"
    have "emeasure ?M {x \<in> space ?M. \<epsilon> \<le> \<bar>X t x - X s x\<bar>}
     \<le> integral\<^sup>N ?M ?inc / \<epsilon> powr a"
      apply (rule nn_integral_Markov_inequality')
      using *(1,2) borel_measurable_diff integrable_X apply blast
      using gt_0(1) *(3) powr_mono2 by (auto intro: mono_onI)
    also have "... \<le> (C * dist t s powr (1 + b)) / ennreal (\<epsilon> powr a)"
      apply (rule divide_right_mono_ennreal)
      using expectation[OF *(1,2)] ennreal_leI by presburger
    finally have "emeasure ?M {x \<in> space ?M. \<epsilon> \<le> \<bar>X t x - X s x\<bar>}
       \<le> (C * dist t s powr (1 + b)) / \<epsilon> powr a"
      using *(3) divide_ennreal gt_0(3) by simp
    then have "\<P>(x in ?M. \<epsilon> \<le> \<bar>X t x - X s x\<bar>) \<le> (C * dist t s powr (1 + b)) / \<epsilon> powr a"
      by (smt (verit, del_insts) divide_nonneg_nonneg ennreal_le_iff gt_0(3) mult_nonneg_nonneg powr_ge_pzero proc_source.emeasure_eq_measure)
  } note markov = this

  text \<open> X s \<longlongrightarrow> X t as s \<longlongrightarrow> t in probability \<close>
  have conv_in_prob: "((\<lambda>s. \<P>(x in ?M. \<epsilon> \<le> \<bar>X t x - X s x\<bar>)) \<longlongrightarrow> 0)(at t within ({0..}))"
    if "t \<ge> 0" "\<epsilon> > 0" for t \<epsilon>
  proof (intro Lim_withinI)
    fix p :: real assume "0 < p"
    let ?q = "(p * \<epsilon> powr a / C) powr (1/(1+b))"
    have "0 < ?q"
      using \<open>0 < p\<close> gt_0(3) that(2) by simp
    have p_eq: "p = (C * ?q powr (1 + b)) / \<epsilon> powr a"
      using gt_0 \<open>0 < ?q\<close> \<open>0 < p\<close> by (simp add: field_simps powr_powr)
    have "\<forall>x\<in>{0..}. 0 < dist x t \<and> dist x t < ?q \<longrightarrow> dist \<P>(xa in proc_source X. \<epsilon> \<le> \<bar>process X t xa - process X x xa\<bar>) 0 \<le> p"
    proof (clarsimp)
      fix s ::real assume "0 \<le> s" "dist s t < ?q"
      then have "C * dist t s powr (1 + b) / \<epsilon> powr a \<le> p"
        by (smt (verit, best) dist_commute divide_less_cancel gt_0(2) gt_0(3) mult_less_cancel_left_pos p_eq powr_ge_pzero powr_less_mono2 zero_le_dist)
      then show "\<P>(x in proc_source X. \<epsilon> \<le> \<bar>process X t x - process X s x\<bar>) \<le> p"
        using markov[OF \<open>0 \<le> s\<close> \<open>0 \<le> t\<close> \<open>0 < \<epsilon>\<close>] by linarith
    qed
    then show "\<exists>d>0. \<forall>x\<in>{0..}. 0 < dist x t \<and> dist x t < d \<longrightarrow> dist \<P>(xa in proc_source X. \<epsilon> \<le> \<bar>process X t xa - process X x xa\<bar>) 0 \<le> p"
      apply (intro exI[where x="?q"])
      using \<open>0 < p\<close> gt_0(3) that(2) by fastforce
  qed

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
  
  We then go on to prove that N is a null set. N characterises the set of points that are
  not Holder continuous, and we can therefore define our continuous modification on M - N.\<close>

  {
    fix T :: real assume "T > 0"
    fix \<gamma> :: real assume "\<gamma> \<in> {0<..<b/a}"
    then have "\<gamma> > 0"
      by auto
    have \<open>\<gamma> \<le> 1\<close>
      by (metis \<open>\<gamma> \<in> {0<..<b/a}\<close> \<open>b \<le> a\<close> greaterThanLessThan_iff gt_0(1) less_divide_eq_1_pos linorder_not_le not_less_iff_gr_or_eq order_less_le_trans)
    have "b - a * \<gamma> > 0"
        using \<open>\<gamma> \<in> {0<..<b/a}\<close> by (simp add: gt_0(1) less_divide_eq mult.commute)
    define A where "A \<equiv> \<lambda>n. if 2 ^ n * T < 1 then {} else 
  {x \<in> space ?M. 
    Max {\<bar>X (real_of_int (k - 1) * 2 powr - real n) x - X (real_of_int k * 2 powr - real n) x\<bar> | k. k \<in> {1..\<lfloor>2^n * T\<rfloor>}}
       \<ge> 2 powr (-\<gamma> * real n)}"
    let ?B = "\<lambda>n. (\<Union>m\<in>{n..}. A m)"
    let ?N = "\<Inter>n \<in> {1..}. ?B n"
    have A_geq: "2 ^ n * T \<ge> 1 \<Longrightarrow> A n = {x \<in> space ?M. 
    Max {\<bar>X (real_of_int (k - 1) * 2 powr - real n) x - X (real_of_int k * 2 powr - real n) x\<bar> | k. k \<in> {1..\<lfloor>2^n * T\<rfloor>}}
       \<ge> 2 powr (-\<gamma> * real n)}" for n
      by (simp add: A_def)
    have A_measurable[measurable]: "A n \<in> sets ?M" for n
      unfolding A_def apply (cases "2 ^ n * T < 1")
       apply simp
      apply (simp only: if_False)
        apply measurable
        apply (metis random_X real_valued)+
      done
    {
      fix n assume [simp]: "2^n * T \<ge> 1"
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
          by (simp add: A_geq)
        from * have "2 powr (- \<gamma> * real n) \<le> Max {\<bar>X (real_of_int (k - 1) * 2 powr - real n) x - X (real_of_int k * 2 powr - real n) x\<bar> |k. k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}}"
          by (simp add: A_geq)
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
          by (fact sum_bounded_above)
        then show ?thesis
          apply (subst proc_source.emeasure_eq_measure)
          apply (subst sum_ennreal)
          apply auto
          apply (rule ennreal_leI)
          apply argo
          done
        qed
      also have "... \<le> C * 2 powr (- n * (1 + b - a * \<gamma>)) * \<lfloor>2 ^ n * T\<rfloor>"
        using \<open>0 < T\<close> by force
      also have "... \<le> C * 2 powr (- n * (1+b - a * \<gamma>)) * 2^n * T"
        by (simp add:ennreal_leI gt_0(3))
      also have "... = C * 1/(2^n) * 2 powr (- n * (b - a * \<gamma>)) * 2^n * T"
        apply (intro ennreal_cong)
        apply (simp add: scale_left_imp_eq field_simps)
        by (smt (verit)\<open>T > 0\<close> \<open>C > 0\<close> powr_add powr_realpow)
      also have "... = C * T * 2 powr (- n * (b - a * \<gamma>))"
        by (simp add: field_simps)
      finally have "emeasure ?M (A n) \<le> C * T * 2 powr (- n * (b - a * \<gamma>))" .
    }
    then have A: "measure ?M (A n) \<le> C * T * 2 powr (- n * (b - a * \<gamma>))" for n
      apply (cases "1 \<le> 2 ^ n * T")
       apply (rule measure_leq_emeasure_ennreal)
      using gt_0(3) \<open>T > 0\<close> apply auto[1]
      apply (simp add: A_geq)
      using \<open>0 < T\<close> gt_0(3) unfolding A_def by force
    have 1: "2 powr (- real x * (b - a * \<gamma>)) = (1 / 2 powr (b - a * \<gamma>)) ^ x" for x
        apply (cases "x = 0")
        by (simp_all add: field_simps powr_add[symmetric] powr_realpow[symmetric] powr_powr)
    have 2: "summable (\<lambda>n. 2 powr (- n * (b - a * \<gamma>)))" (is "summable ?C")
    proof -
      have "summable (\<lambda>n. (1 / 2 powr (b - a * \<gamma>)) ^ n)"
        using \<open>b - a * \<gamma> > 0\<close> by auto
      then show "summable (\<lambda>x. 2 powr (- real x * (b - a * \<gamma>)))"
        using 1 by simp
    qed
    have "(\<Sum>n. (C * T) * 2 powr (- n * (b - a * \<gamma>))) = C * T * 2 powr (b - \<gamma> * a) / (2 powr (b - \<gamma> * a) - 1)"
    proof -
      have "(\<Sum>n. (C * T) * 2 powr (- n * (b - a * \<gamma>))) = (C * T) * (\<Sum>n. 2 powr (- n * (b - a * \<gamma>)))"
        by (fact suminf_mult[OF 2])
      moreover have "(\<Sum>n. 2 powr (- n * (b - a * \<gamma>))) = 1/(1- (1/2 powr (b - a * \<gamma>)))"
        apply (subst 1)
        apply (rule suminf_geometric)
        using \<open>0 < b - a * \<gamma>\<close> by auto
      also have "... = 2 powr (b - \<gamma> * a) / (2 powr (b - \<gamma> * a) - 1)"
        by (simp add: field_simps)
      finally show ?thesis
        by force
    qed
    have summable_A: "summable (\<lambda>m. Sigma_Algebra.measure (proc_source X) (A m))"
      apply (rule summable_comparison_test_ev)
       apply (rule eventuallyI)
       apply simp
       apply (fact A)
      using 2 summable_mult by blast
    then have "summable (\<lambda>m. Sigma_Algebra.measure (proc_source X) (A (m + n)))" for n
      by (subst summable_iff_shift)
    {
      fix n
      have "measure ?M (?B n) \<le> (\<Sum>m. measure ?M (A (m + n)))"
        sorry
      also have "... \<le> C * T * (2 powr (b - \<gamma> * a) / (2 powr (b - \<gamma> * a) - 1) - (\<Sum>m<n. measure ?M (A m)))"
        sorry
      finally have "measure ?M (?B n) \<le> C * T * (2 powr (b - \<gamma> * a) / (2 powr (b - \<gamma> * a) - 1) - (\<Sum>m<n. measure ?M (A m)))"
        .
    }
    then have "(\<lambda>n. measure ?M (?B n)) \<longlonglongrightarrow> 0"
      sorry
    then have N_null: "?N \<in> null_sets ?M"
      sorry

    {
      fix \<omega> assume \<omega>: "\<omega> \<in> space ?M - ?N"
      then obtain n\<^sub>0 :: nat where "\<omega> \<notin> (\<Union>n \<in> {n\<^sub>0..}. A n)"
        by blast
      then have "norm (X (real_of_int k/2^n) \<omega> - X ((real_of_int k-1)/2^n) \<omega>) < 2 powr (- \<gamma> * n)"
        if "k \<in> {1..\<lfloor>2^n * T\<rfloor>}" "n \<ge> n\<^sub>0" for n k
        using that sorry
  
      text \<open> The objective of this block is to show that, for dyadic numbers s t with the same resolution:
     | X t \<omega> - x s \<omega> | \<le> 2 * 2 powr (- \<gamma> * n) / (1 - 2 powr - \<gamma>)
    Holder continuity on dyadic numbers follows directly from this fact.
  \<close>
  
      {
        fix m n :: nat assume mn: "m \<ge> n" "n \<ge> n\<^sub>0"
        fix s t :: real 
          assume s_dyadic: "s \<in> dyadic_interval m 0 T"
          and t_dyadic: "t \<in> dyadic_interval m 0 T"
          and st: "s \<le> t" "norm (s - t) \<le> 1/2^n"
        let ?u = "\<lfloor>2^n * s\<rfloor> / 2^n"
        have "?u = Max (dyadic_interval n 0 s)"
          apply (rule dyadic_interval_Max[symmetric])
          apply (rule dyadics_geq[OF s_dyadic])
          done
        have "?u \<le> s"
          using floor_pow2_leq by blast
        have "s < ?u + 1/2^n"
          apply (simp add: field_simps)
          using floor_le_iff apply linarith
          done
        have "?u \<le> t"
          using \<open>?u \<le> s\<close> st(1) by linarith
        have "t < ?u + 2/2^n"
          using \<open>s <?u + 1/2^n\<close> st(2) by force
        obtain bt kt where t_exp: "bt \<in> {1..m} \<rightarrow>\<^sub>E {0,1}" "kt \<in> {0..\<lfloor>T\<rfloor>}" "t = kt + (\<Sum>m\<in>{1..m}. bt m / 2 ^ m)"
          using t_dyadic dyadic_expansion by meson
        obtain bs ks where s_exp: "bs \<in> {1..m} \<rightarrow>\<^sub>E {0,1}" "ks \<in> {0..\<lfloor>T\<rfloor>}" "s = ks + (\<Sum>m\<in>{1..m}. bs m / 2 ^ m)"
          using s_dyadic dyadic_expansion by meson
        have "(bs i - ?u) = 0" if \<open>i < n\<close> for i
          sorry
        have "(bt i - ?u) = 0" if \<open>i < n\<close> for i
          sorry
        have "dist (X t \<omega>) (X s \<omega>) \<le> 2 * 2 powr (- \<gamma> * n) / (1 - 2 powr - \<gamma>)"
          sorry
      } note dist_dyadic = this
  
      text \<open> We show that for dyadic rationals, X is Holder-continuous \<close>
      let ?C\<^sub>0 = "2 powr (1 + \<gamma>) / (1 - 2 powr - \<gamma>)"
      have "?C\<^sub>0 > 0"
        by (smt (verit) \<open>\<gamma> > 0\<close> \<open>\<gamma> \<le> 1\<close> less_divide_eq_1_pos powr_eq_one_iff powr_ge_pzero powr_le_cancel_iff)
      {
        fix s t
        assume s: "s \<in> (\<Union>n. dyadic_interval n 0 T)"
           and t: "t \<in> (\<Union>n. dyadic_interval n 0 T)"
           and st_dist: "dist t s \<le> 1 / 2 ^ n\<^sub>0"
           and neq: "s \<noteq> t"
        then have "dist t s > 0"
          using neq by simp
        then have "\<exists>n. dist t s \<ge> 1 / 2^n \<and> n \<ge> n\<^sub>0"
        proof -
          obtain n where n: "1 / 2^n \<le> dist t s"
            by (metis \<open>0 < dist t s\<close> less_eq_real_def one_less_numeral_iff power_one_over reals_power_lt_ex semiring_norm(76))
          then have "1 / 2 ^ (n + n\<^sub>0) \<le> dist t s"
            using mult_mono[of "dist t s * 2 ^ n" "dist t s * 2 ^ n" "1" "2 ^ n\<^sub>0"] 
            by (simp add: power_add field_simps)
          then show ?thesis
            by auto
        qed
        then have "dist (X t \<omega>) (X s \<omega>) \<le> ?C\<^sub>0 * (dist t s) powr \<gamma>"
          sorry
      } note dist_dyadic = this
      let ?K = "\<lambda>t s. ?C\<^sub>0 * 2 powr ((1-\<gamma>) * n\<^sub>0) * (dist t s) powr \<gamma>"
      have X_incr: "dist (X t \<omega>) (X s \<omega>) \<le> ?K t s"
        if "s \<in> (\<Union>n. dyadic_interval n 0 T)" and "t \<in> (\<Union>n. dyadic_interval n 0 T)"
        for s t
        using dist_dyadic sorry
      then have holder_dyadic: "\<gamma>-holder_on (\<Union>n. dyadic_interval n 0 T) (\<lambda>t. X t \<omega>)"
        apply (intro holder_onI)
        using \<open>0 < \<gamma>\<close> apply blast
        using \<open>\<gamma> \<le> 1\<close> apply blast
        apply (intro exI[where x="?C\<^sub>0 * 2 powr ((1-\<gamma>) * n\<^sub>0)"])
        using \<open>?C\<^sub>0 > 0\<close> apply (auto simp: \<open>?C\<^sub>0 > 0\<close>zero_less_divide_iff)
        done
      then have "uniformly_continuous_on (\<Union>n. dyadic_interval n 0 T) (\<lambda>t. X t \<omega>)"
        by (fact holder_uniform_continuous)
      then have "\<exists>L. ((\<lambda>s. X s \<omega>) \<longlongrightarrow> L) (at t within (\<Union>n. dyadic_interval n 0 T))"
        if "t \<in> {0..T} - (\<Union>n. dyadic_interval n 0 T)" for t
        apply (rule uniformly_continuous_on_extension_at_closure[where x = t])
        using that dyadic_interval_dense apply fast
        apply fast
        done
      define L where
          "L \<equiv> (\<lambda>t. (THE L. ((\<lambda>s. X s \<omega>) \<longlongrightarrow> L) (at t within (\<Union>n. dyadic_interval n 0 T))))"
      define X_tilde :: "real \<Rightarrow> real" where
        "X_tilde \<equiv> \<lambda>t. if t \<in> (\<Union>n. dyadic_interval n 0 T) then X t \<omega> else L t"
      then have "dist (X_tilde s) (X_tilde t) \<le> ?K s t" if "s \<in> {0..T}" "t \<in> {0..T}" for s t
        sorry text \<open> Should be analogous to the proof of @{thm dist_dyadic} \<close>
      then have "\<gamma>-holder_on {0..T} X_tilde"
        apply (intro holder_onI)
        using \<open>0 < \<gamma>\<close> apply blast
        using \<open>\<gamma> \<le> 1\<close> apply blast
        apply (intro exI[where x="?C\<^sub>0 * 2 powr ((1-\<gamma>) * n\<^sub>0)"])
        using \<open>?C\<^sub>0 > 0\<close> apply (auto simp: \<open>?C\<^sub>0 > 0\<close>zero_less_divide_iff)
        done
      then have "local_holder_on \<gamma> {0..T} X_tilde"
        using holder_implies_local_holder by blast
    } note X_tilde_arb_omega = this (* GIVE BETTER NAME *)
    define X_tilde :: "real \<Rightarrow> 'a \<Rightarrow> real" where
    "X_tilde \<equiv> (\<lambda>t \<omega>. if \<omega> \<in> ?N then 0 else
                      (if t \<in> (\<Union>n. dyadic_interval n 0 T) then X t \<omega> else THE L. ((\<lambda>s. X s \<omega>) \<longlongrightarrow> L) (at t within (\<Union>n. dyadic_interval n 0 T))))"
    have local_holder_X_tilde: "local_holder_on \<gamma> {0..T} (\<lambda>t. X_tilde t \<omega>)" if "\<omega> \<in> space ?M" for \<omega>
    proof (cases "\<omega> \<in> ?N")
      case True
      then show ?thesis 
        unfolding X_tilde_def by (simp add: local_holder_const \<open>0 < \<gamma>\<close> \<open>\<gamma> \<le> 1\<close>)
    next
      case False
      then have 1: "\<omega> \<in> space ?M - ?N"
        using that by blast
      show ?thesis
        unfolding X_tilde_def by (simp only: False if_False X_tilde_arb_omega[OF 1])
    qed
    have "AE \<omega> in ?M. X t \<omega> = X_tilde t \<omega>" if "t \<in> {0..T}" for t
    proof (cases "t \<in> (\<Union>n. dyadic_interval n 0 T)")
      case True
      then have "\<omega> \<notin> ?N \<Longrightarrow> X t \<omega> = X_tilde t \<omega>" for \<omega>
        unfolding X_tilde_def by (simp only: if_True if_False)
      then have "{\<omega>. X t \<omega> \<noteq> X_tilde t \<omega>} \<subseteq> ?N"
        by blast
      then show ?thesis
        apply (intro AE_I[where N="?N"])
        using N_null by auto
    next
      case False
      then show ?thesis
        using conv_in_prob[of t] sorry
    qed
    moreover have X_tilde_measurable: "X_tilde t \<in> borel_measurable ?M" if "t \<in> {0..T}" for t
      unfolding X_tilde_def apply measurable
         apply (metis random_X real_valued)
        defer
      using sets.sets_Collect_const apply blast
       apply auto[1]
      sorry (* Prove limit is measurable *)
    ultimately have "modification (restrict_index X {0..T}) (process_of (proc_source X) (proc_target X) {0..T} X_tilde 0)"
      apply (intro modificationI)
      unfolding compatible_def apply safe
           apply (simp_all add: proc_source.prob_space_axioms real_valued)
      by (metis restrict_index_source)
    then have "\<exists>Y. modification (restrict_index X {0..T}) Y \<and> (\<forall>x \<in> space (proc_source X). local_holder_on \<gamma> {0..T} (\<lambda>t. process Y t x))"
      apply (intro exI[where x="(process_of (proc_source X) (proc_target X) {0..T} X_tilde 0)"])
      apply safe
      apply (subst process_process_of)
         apply (simp_all add: proc_source.prob_space_axioms real_valued X_tilde_measurable)
      using local_holder_X_tilde unfolding local_holder_on_def by auto
  } note * = this
  define Mod where "Mod \<equiv> \<lambda>T \<gamma>. SOME Y. modification (restrict_index X {0..T}) Y \<and> 
    (\<forall>x\<in>space (proc_source X). local_holder_on \<gamma> {0..T} (\<lambda>t. Y t x))"
  have Mod_source[simp]: "\<lbrakk>T > 0; \<gamma> \<in> {0<..<b/a}\<rbrakk> \<Longrightarrow> proc_source (Mod T \<gamma>) = proc_source X" for T \<gamma>
    unfolding Mod_def using someI * apply simp
    by (smt (verit, del_insts) compatible_source modificationD(1) restrict_index_source someI)
  have Mod: "modification (restrict_index X {0..T}) (Mod T \<gamma>) \<and> 
    (\<forall>x\<in>space (proc_source X). local_holder_on \<gamma> {0..T} (\<lambda>t. (Mod T \<gamma>) t x)) " if "0 < T" "\<gamma> \<in> {0<..<b/a}" for T \<gamma>
    using someI_ex[OF *[OF that]] unfolding Mod_def by blast
  {
    fix S T ::real assume ST[simp]: "S > 0" "T > 0"
    fix \<gamma> :: real assume gamma: "\<gamma> \<in> {0<..<b/a}"
    have mod_restrict: "modification (restrict_index (Mod S \<gamma>) {0..min S T}) (restrict_index (Mod T \<gamma>) {0..min S T})"
    proof -
      have "modification (restrict_index X {0..min S T}) (restrict_index (Mod S \<gamma>) {0..min S T})"
        using restrict_index_override modification_restrict_index Mod[OF ST(1) gamma] by fastforce
      moreover have "modification (restrict_index X {0..min S T}) (restrict_index (Mod T \<gamma>) {0..min S T})"
        using restrict_index_override modification_restrict_index Mod[OF ST(2) gamma] by fastforce
      ultimately show ?thesis
        using modification_sym modification_trans by blast
    qed
    then have *: "indistinguishable (restrict_index (Mod S \<gamma>) {0..min S T}) (restrict_index (Mod T \<gamma>) {0..min S T})"
    proof -
      have "\<forall>x \<in> space ?M. continuous_on {0..S} (\<lambda>t. (Mod S \<gamma>) t x)"
        using Mod[OF ST(1) gamma] local_holder_continuous by blast
      then have 1: "\<forall>x \<in> space ?M. continuous_on {0..min S T} (\<lambda>t. (Mod S \<gamma>) t x)"
        using continuous_on_subset by fastforce
      have "\<forall>x \<in> space ?M. continuous_on {0..T} (\<lambda>t. (Mod T \<gamma>) t x)"
        using Mod[OF ST(2) gamma] local_holder_continuous by fast
      then have 2: "\<forall>x \<in> space ?M. continuous_on {0..min S T} (\<lambda>t. (Mod T \<gamma>) t x)"
        using continuous_on_subset by fastforce
      show ?thesis
        apply (rule modification_continuous_indistinguishable)
           apply (fact mod_restrict)
        using ST(1) ST(2) apply (smt (verit, best) restrict_index_index)
         apply (intro AE_I2, simp)
        using "1" gamma apply fastforce
        apply (intro AE_I2, simp)
        apply (metis "2" ST(2) Mod_source gamma)
        done
    qed
  }
  then have "\<And>S T. S > 0 \<Longrightarrow> T > 0 \<Longrightarrow> \<exists>N \<in> null_sets (proc_source X). {\<omega> \<in> space (proc_source X). \<exists>t \<in> {0..min S T}.
   (restrict_index (Mod S \<gamma>) {0..min S T}) t \<omega> \<noteq> (restrict_index (Mod S \<gamma>) {0..min S T}) t \<omega>} \<subseteq> N" if "\<gamma> \<in> {0<..<b / a}" for \<gamma>
    using indistinguishable_null_ex that by blast
  then obtain N where N: "S > 0 \<Longrightarrow> T > 0 \<Longrightarrow> N \<gamma> S T \<in> null_sets (proc_source X) \<and> {\<omega> \<in> space (proc_source X). \<exists>t \<in> {0..min S T}.
   (restrict_index (Mod S \<gamma>) {0..min S T}) t \<omega> \<noteq> (restrict_index (Mod S \<gamma>) {0..min S T}) t \<omega>} \<subseteq> N \<gamma> S T" if "\<gamma> \<in> {0<..<b / a}" for \<gamma> T S
    by meson
  then have "(\<Union>S \<in> \<nat> - {0}. (\<Union> T \<in> \<nat> - {0}. N \<gamma> S T)) \<in> null_sets ?M" if "\<gamma> \<in> {0<..<b / a}" for \<gamma>
    apply (intro null_sets_UN')
     apply (rule countable_Diff)
      apply (simp add: Nats_def)+
    using that by force
  define X_mod where "X_mod \<equiv> (\<lambda>t \<omega>. (Mod \<lceil>t\<rceil> \<gamma>) t \<omega>)"
  
  show ?thesis
    apply (rule exI[where x="process_of ?M (proc_target X) {0..} (X_mod) 0"])
    sorry
qed

end