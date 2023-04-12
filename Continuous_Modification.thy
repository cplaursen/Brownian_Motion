theory Continuous_Modification
  imports Stochastic_Process Holder_Continuous Dyadic_Interval
begin

text \<open> Klenke 5.11: Markov inequality. Compare with @{thm nn_integral_Markov_inequality} \<close>

lemma nn_integral_Markov_inequality_extended:
  fixes f :: "real \<Rightarrow> ennreal" and \<epsilon> :: real and X :: "'a \<Rightarrow> real"
  assumes X[measurable]: "X \<in> borel_measurable M"
      and mono: "mono f"
      and finite: "\<And>x. f x < \<infinity>"
      and e: "\<epsilon> > 0" "f \<epsilon> > 0"
    shows "emeasure M {p \<in> space M. (X p) \<ge> \<epsilon>} \<le> (\<integral>\<^sup>+ x. f (X x) \<partial>M) / f \<epsilon>"
proof -
  have f_eq: "f = (\<lambda>x. ennreal (enn2real (f x)))"
    using finite by simp
  moreover have "mono (\<lambda>x. enn2real (f x))"
    apply (intro monotoneI)
    apply (subst enn2real_mono)
    using mono[THEN monotoneD] finite by simp_all
  ultimately have "(\<lambda>x. f (X x)) \<in> borel_measurable M"
    apply (intro measurable_compose[where g=f and f=X])
     apply measurable
    apply (metis borel_measurable_mono measurable_compose_rev measurable_ennreal)
    done
  then have "{x \<in> space M. f (X x) \<ge> f \<epsilon>} \<in> sets M"
    by measurable
  then have "f \<epsilon> * emeasure M {p \<in> space M. X p \<ge> \<epsilon>} \<le> \<integral>\<^sup>+x\<in>{x \<in> space M. f \<epsilon> \<le> f (X x)}. f \<epsilon> \<partial>M"
    apply (simp add: nn_integral_cmult_indicator)
    apply (rule mult_left_mono)
     apply (rule emeasure_mono)
      apply simp_all
      using e mono_onD[OF mono] apply auto
    done
  also have "... \<le> \<integral>\<^sup>+x\<in>{x \<in> space M. f \<epsilon> \<le> f (X x)}. f (X x)\<partial>M"
    apply (rule nn_integral_mono)
    subgoal for x
      apply (cases "f \<epsilon> \<le> f (X x)")
      using ennreal_leI by auto
    done
  also have "... \<le> \<integral>\<^sup>+ x. f (X x) \<partial>M"
    by (simp add: divide_right_mono_ennreal nn_integral_mono indicator_def)
  finally show ?thesis
  proof -
    assume "f \<epsilon> * emeasure M {p \<in> space M. \<epsilon> \<le> ( (X p))} \<le> \<integral>\<^sup>+ x. (f (X x)) \<partial>M"
    then have "(f \<epsilon> * emeasure M {p \<in> space M. \<epsilon> \<le> ( (X p))}) / f \<epsilon> \<le> (\<integral>\<^sup>+ x. (f (X x)) \<partial>M) / f \<epsilon>"
      by (fact divide_right_mono_ennreal)
    moreover have "(f \<epsilon> * emeasure M {p \<in> space M. \<epsilon> \<le> (X p)}) / f \<epsilon> = emeasure M {p \<in> space M. \<epsilon> \<le> (X p)}"
    proof -
      have "(f \<epsilon> * emeasure M {p \<in> space M. \<epsilon> \<le> (X p)}) / f \<epsilon> = emeasure M {p \<in> space M. \<epsilon> \<le> (X p)} * f \<epsilon> / f \<epsilon>"
        by (simp add: field_simps)
      also have "... = emeasure M {p \<in> space M. \<epsilon> \<le> (X p)}"
        by (metis (no_types, lifting) e(2) ennreal_mult_divide_eq infinity_ennreal_def finite order_less_irrefl)
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by argo
  qed
qed

lemma nn_integral_Markov_inequality_rnv:
  fixes f :: "real \<Rightarrow> real" and \<epsilon> :: real and X :: "'a \<Rightarrow> 'b :: real_normed_vector"
  assumes X[measurable]: "X \<in> borel_measurable M"
      and mono: "mono_on {0..} f"
      and e: "\<epsilon> > 0" "f \<epsilon> > 0"
    shows "emeasure M {p \<in> space M. norm (X p) \<ge> \<epsilon>} \<le> (\<integral>\<^sup>+ x. f (norm (X x)) \<partial>M) / f \<epsilon>"
proof -
  have "(\<lambda>x. f (norm (X x))) \<in> borel_measurable M"
    apply (rule measurable_compose[of "\<lambda>x. norm (X x)" M "restrict_space borel {0..}"])
     apply (subst measurable_restrict_space2_iff)
     apply auto[1]
    apply (fact borel_measurable_mono_on_fnc[OF mono])
    done
  then have "{x \<in> space M. f (norm (X x)) \<ge> f \<epsilon>} \<in> sets M"
    by measurable
  then have "f \<epsilon> * emeasure M {p \<in> space M. norm (X p) \<ge> \<epsilon>} \<le> \<integral>\<^sup>+x\<in>{x \<in> space M. f \<epsilon> \<le> f (norm (X x))}. f \<epsilon> \<partial>M"
    apply (simp add: nn_integral_cmult_indicator)
    apply (rule mult_left_mono)
     apply (rule emeasure_mono)
      apply simp_all
      using e mono_onD[OF mono] apply auto
    done
  also have "... \<le> \<integral>\<^sup>+x\<in>{x \<in> space M. f \<epsilon> \<le> f (norm (X x))}. f (norm (X x))\<partial>M"
    apply (rule nn_integral_mono)
    subgoal for x
      apply (cases "f \<epsilon> \<le> f (norm (X x))")
      using ennreal_leI by auto
    done
  also have "... \<le> \<integral>\<^sup>+ x. f (norm (X x)) \<partial>M"
    by (simp add: divide_right_mono_ennreal nn_integral_mono indicator_def)
  finally show ?thesis
  proof -
    assume "f \<epsilon> * emeasure M {p \<in> space M. \<epsilon> \<le> (norm (X p))} \<le> \<integral>\<^sup>+ x. (f (norm (X x))) \<partial>M"
    then have "(f \<epsilon> * emeasure M {p \<in> space M. \<epsilon> \<le> (norm (X p))}) / f \<epsilon> \<le> (\<integral>\<^sup>+ x. (f (norm (X x))) \<partial>M) / f \<epsilon>"
      by (fact divide_right_mono_ennreal)
    moreover have "(f \<epsilon> * emeasure M {p \<in> space M. \<epsilon> \<le> (norm (X p))}) / f \<epsilon> = emeasure M {p \<in> space M. \<epsilon> \<le> (norm (X p))}"
    proof -
      have "(f \<epsilon> * emeasure M {p \<in> space M. \<epsilon> \<le> (norm (X p))}) / f \<epsilon> = emeasure M {p \<in> space M. \<epsilon> \<le> (norm (X p))} * f \<epsilon> / f \<epsilon>"
        by (simp add: field_simps)
      also have "... = emeasure M {p \<in> space M. \<epsilon> \<le> (norm (X p))}"
        using e(2) ennreal_mult_divide_eq by force
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by argo
  qed
qed

lemma Max_finite_image_ex:
  assumes "finite S" "S \<noteq> {}" "P (MAX k\<in>S. f k)" 
  shows "\<exists>k \<in> S. P (f k)"
  using bexI[of P "Max (f ` S)" "f ` S"] by (simp add: assms)

lemma measure_leq_emeasure_ennreal: "0 \<le> x \<Longrightarrow> emeasure M A \<le> ennreal x \<Longrightarrow> measure M A \<le> x"
  apply (cases "A \<in> M")
   apply (metis Sigma_Algebra.measure_def enn2real_leI)
   apply (auto simp: measure_notin_sets emeasure_notin_sets)
  done

lemma Union_add_subset: "(m :: nat) \<le> n \<Longrightarrow> (\<Union>k. A (k + n)) \<subseteq> (\<Union>k. A (k + m))"
  apply (subst subset_eq)
  apply simp
  apply (metis add.commute le_iff_add trans_le_add1)
  done

lemma floor_in_Nats: "x \<ge> 0 \<Longrightarrow> \<lfloor>x\<rfloor> \<in> \<nat>"
  by (metis nat_0_le of_nat_in_Nats zero_le_floor)

text \<open> Klenke 21.6 - Kolmorogov-Chentsov\<close>

text_raw \<open>\DefineSnippet{holder_continuous_modification}{\<close>
theorem holder_continuous_modification:
  fixes X :: "(real, 'a, 'b :: polish_space) stochastic_process"
  assumes index[simp]: "proc_index X = {0..}"
      and target_borel[measurable, simp]: "proc_target X = borel"
      and gt_0: "a > 0" "b > 0" "C > 0"
      and "b \<le> a" (* Probably follows from other assms *)
      and gamma: "\<gamma> \<in> {0<..<b/a}"
      and expectation: "\<And>s t. \<lbrakk>s \<ge> 0; t \<ge> 0\<rbrakk> \<Longrightarrow>
          (\<integral>\<^sup>+ x. dist (X t x) (X s x) powr a \<partial>proc_source X) \<le> C * dist t s powr (1+b)"
    shows "\<exists>Y. modification X Y \<and> (\<forall>x \<in> space (proc_source X). local_holder_on \<gamma> {0..} (\<lambda>t. Y t x))"
text_raw \<open>}%EndSnippet\<close>
proof -
  let ?M = "proc_source X"
  have "0 < \<gamma>" "\<gamma> < 1"
    using gamma apply simp
    by (metis assms(6) divide_le_eq_1_pos gamma greaterThanLessThan_iff gt_0(1) order_less_le_trans)
  then have "\<gamma> \<in> {0<..1}"
    by simp
  text \<open> Consequence of @{thm nn_integral_Markov_inequality_extended} \<close>
  have markov: "\<P>(x in ?M. \<epsilon> \<le> dist (X t x) (X s x)) \<le> (C * dist t s powr (1 + b)) / \<epsilon> powr a"
    if "s \<ge> 0" "t \<ge> 0" "\<epsilon> > 0" for s t \<epsilon>
  proof -
    let ?inc = "\<lambda>x. dist (X t x) (X s x) powr a"
    have "emeasure ?M {x \<in> space ?M. \<epsilon> \<le> dist (X t x) (X s x)}
     \<le> integral\<^sup>N ?M ?inc / \<epsilon> powr a"
      apply (rule nn_integral_Markov_inequality_extended)
      using that(1,2) apply measurable
        apply (metis random_process target_borel)
          apply (metis random_process target_borel)
         apply (intro monoI)
         apply (subst ennreal_le_iff2)
         apply auto
      sorry
    also have "... \<le> (C * dist t s powr (1 + b)) / ennreal (\<epsilon> powr a)"
      apply (rule divide_right_mono_ennreal)
      using expectation[OF that(1,2)] ennreal_leI by simp
    finally have "emeasure ?M {x \<in> space ?M. \<epsilon> \<le> dist (X t x) (X s x)}
       \<le> (C * dist t s powr (1 + b)) / \<epsilon> powr a"
      using that(3) divide_ennreal gt_0(3) by simp
    moreover have "C * dist t s powr (1 + b) / \<epsilon> powr a \<ge> 0"
      using gt_0(3) by auto
    ultimately show ?thesis
      by (simp add: proc_source.emeasure_eq_measure)
  qed

  text \<open> X s \<longlongrightarrow> X t as s \<longlongrightarrow> t in probability \<close>
  have conv_in_prob: "((\<lambda>s. \<P>(x in ?M. \<epsilon> \<le> dist (X t x) (X s x))) \<longlongrightarrow> 0)(at t within ({0..}))"
    if "t \<ge> 0" "\<epsilon> > 0" for t \<epsilon>
  proof (intro Lim_withinI)
    fix p :: real assume "0 < p"
    let ?q = "(p * \<epsilon> powr a / C) powr (1/(1+b))"
    have "0 < ?q"
      using \<open>0 < p\<close> gt_0(3) that(2) by simp
    have p_eq: "p = (C * ?q powr (1 + b)) / \<epsilon> powr a"
      using gt_0 \<open>0 < ?q\<close> \<open>0 < p\<close> by (simp add: field_simps powr_powr)
    have "0 < dist r t \<and> dist r t < ?q \<longrightarrow> dist \<P>(x in ?M. \<epsilon> \<le> dist (X t x) (X r x)) 0 \<le> p"
      if "r \<in> {0..}" for r
    proof (clarsimp)
      assume "r \<noteq> t" "dist r t < ?q"
      have "0 \<le> r"
        using that by auto
      from \<open>dist r t < ?q\<close> have "C * dist r t powr (1 + b) / \<epsilon> powr a \<le> p"
        apply (subst p_eq)
        using gt_0(2) gt_0(3) apply (simp add: divide_le_cancel powr_mono2)
        done
      then show "\<P>(x in ?M. \<epsilon> \<le> dist (X t x) (X r x)) \<le> p"
        using markov[OF \<open>0 \<le> r\<close> \<open>0 \<le> t\<close> \<open>0 < \<epsilon>\<close>] by (simp add: dist_commute)
    qed
    then show "\<exists>d>0. \<forall>r\<in>{0..}. 0 < dist r t \<and> dist r t < d \<longrightarrow> dist \<P>(x in ?M. \<epsilon> \<le> dist (X t x) (X r x)) 0 \<le> p"
      apply (intro exI[where x="?q"])
      using \<open>0 < p\<close> gt_0(3) that(2) by fastforce
  qed

  have incr: "\<P>(x in ?M. 2 powr (- \<gamma> * n) \<le> dist (X ((k - 1) * 2 powr - n) x) (X (k * 2 powr - n) x))
         \<le> C * 2 powr (-n * (1+b-a*\<gamma>))"
    if "\<gamma> > 0" "k \<ge> 1" "n \<ge> 0" for \<gamma> k n
  proof -
    have "\<P>(x in ?M. 2 powr (- \<gamma> * n) \<le> dist (X ((k - 1) * 2 powr - n) x) (X (k * 2 powr - n) x))
         \<le> C * dist ((k - 1) * 2 powr - n) (k * 2 powr - n) powr (1 + b) / (2 powr (- \<gamma> * n)) powr a"
      apply (rule markov)
      using that by auto
    also have "... = C * 2 powr (- n - b * n) / 2 powr (- \<gamma> * n * a)"
      by (auto simp: dist_real_def that powr_powr field_simps)
    also have "... =  C * 2 powr (-n * (1+b-a*\<gamma>))"
      apply (auto simp: field_simps)
      by (smt (verit) powr_add)
    finally show ?thesis .
  qed
    
  text \<open> In the textbook, we define the following:
  A_n(\<gamma>) = {x. max {dist (X ((k - 1) * 2 powr - n) x) (X (k * 2 powr - n) x), k \<in> {0..2^n}} \<ge> 2 powr -\<gamma> * n}
  B_n = \<Union>m\<ge>n. A_m
  N = limsup (n -> \<infinity>) A_n = \<Inter>n. B_n
  
  We then go on to prove that N is a null set. N characterises the set of points that are
  not Holder continuous, and we can therefore define our continuous modification on M - N.\<close>

  {
    fix T :: real assume "T > 0"
    define A where "A \<equiv> \<lambda>n. if 2 ^ n * T < 1 then space ?M else 
  {x \<in> space ?M. 
    Max {dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x)
       | k. k \<in> {1..\<lfloor>2^n * T\<rfloor>}} \<ge> 2 powr (-\<gamma> * real n)}"
    let ?B = "\<lambda>n. (\<Union>m. A (m + n))"
    let ?N = "\<Inter> (range ?B)"
    have A_geq: "2 ^ n * T \<ge> 1 \<Longrightarrow> A n = {x \<in> space ?M. 
    Max {dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x)
   | k. k \<in> {1..\<lfloor>2^n * T\<rfloor>}} \<ge> 2 powr (-\<gamma> * real n)}" for n
      by (simp add: A_def)
    have A_measurable[measurable]: "A n \<in> sets ?M" for n
      unfolding A_def apply (cases "2 ^ n * T < 1")
       apply simp
      apply (simp only: if_False)
        apply measurable
        apply (metis random_process target_borel)+
      done
    have "emeasure ?M (A n) \<le> ennreal (C * T * 2 powr (real_of_int (- int n) * (b - a * \<gamma>)))"
      if [simp]: "2^n * T \<ge> 1" for n
    proof -
      have nonempty: "{1..\<lfloor>2^n * T\<rfloor>} \<noteq> {}"
        using that by fastforce
      have finite: "finite {1..\<lfloor>2^n * T\<rfloor>}"
        by simp
      have "emeasure ?M (A n) \<le> emeasure ?M (\<Union>k \<in> {1..\<lfloor>2^n * T\<rfloor>}.
      {x\<in>space ?M. dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x) \<ge> 2 powr (- \<gamma> * real n)})"
      (is "emeasure ?M (A n) \<le> emeasure ?M ?R")
      proof (rule emeasure_mono, intro subsetI)
        fix x assume *: "x \<in> A n"
        from * have in_space: "x \<in> space ?M"
          by (simp add: A_geq)
        from * have "2 powr (- \<gamma> * real n) \<le> Max {dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x) |k. k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}}"
          by (simp add: A_geq)
        then have "\<exists>k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}. 2 powr (- \<gamma> * real n) \<le> dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x)"
          apply (simp only: setcompr_eq_image)
          apply (rule Max_finite_image_ex[where P="\<lambda>x. 2 powr (- \<gamma> * real n) \<le> x", OF finite nonempty])
          apply (metis Collect_mem_eq)
          done
        then show "x \<in> ?R"
          using in_space by simp
      next
        show "?R \<in> sets ?M"
          apply measurable
          by (smt (verit) target_borel random_process)+
      qed
      also have "... \<le> (\<Sum>k\<in>{1..\<lfloor>2^n * T\<rfloor>}. emeasure ?M 
    {x\<in>space ?M. dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x) \<ge> 2 powr (- \<gamma> * real n)})"
        apply (rule emeasure_subadditive_finite)
         apply blast
        apply (subst image_subset_iff)
        apply (intro ballI)
        apply measurable
         apply (metis random_process target_borel)+
        done
      also have "... \<le> C * 2 powr (- n * (1 + b - a * \<gamma>)) * (card {1..\<lfloor>2 ^ n * T\<rfloor>})"
      proof -
        {
          fix k assume "k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}"
          then have "real_of_int k \<ge> 1"
            by presburger
          then have "\<P>(x in ?M. 2 powr (- \<gamma> * real n) \<le> dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x))
                 \<le> C * 2 powr (-(real n) * (1+b-a*\<gamma>))"
            using incr[OF \<open>\<gamma> > 0\<close>] by simp
        } note X = this
        then have "sum (\<lambda>k. \<P>(x in ?M. 2 powr (- \<gamma> * real n) \<le> dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x))) 
                        {1..\<lfloor>2 ^ n * T\<rfloor>} \<le> of_nat (card {1..\<lfloor>2 ^ n * T\<rfloor>}) * (C * 2 powr (-(real n) * (1+b-a*\<gamma>)))"
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
      finally show "emeasure ?M (A n) \<le> C * T * 2 powr (- n * (b - a * \<gamma>))" .
    qed
    then have A: "measure ?M (A n) \<le> C * T * 2 powr (- n * (b - a * \<gamma>))" if "2^n * T \<ge> 1" for n
      apply (intro measure_leq_emeasure_ennreal)
        using gt_0(3) \<open>T > 0\<close> apply auto[1]
        apply (simp add: A_geq that)
      done
    have "b - a * \<gamma> > 0"
        using \<open>\<gamma> \<in> {0<..<b/a}\<close> by (simp add: gt_0(1) less_divide_eq mult.commute)
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
    have "summable (\<lambda>m. measure ?M (A m))"
    proof -
      from \<open>0 < T\<close> obtain N where "2^N * T \<ge> 1"
        by (metis dual_order.order_iff_strict mult.commute one_less_numeral_iff pos_divide_le_eq
            power_one_over reals_power_lt_ex semiring_norm(76) zero_less_numeral zero_less_power)
      then have "\<And>n. n \<ge> N \<Longrightarrow> 2^n * T \<ge> 1" 
        by (smt (verit, best) \<open>0 < T\<close> mult_right_mono power_increasing_iff)
      then have "\<And>n. n \<ge> N \<Longrightarrow> norm (measure ?M (A n)) \<le> C * T * 2 powr (- n * (b - a * \<gamma>))"
        using A by simp
      moreover have "summable (\<lambda>n. C * T * 2 powr (- n * (b - a * \<gamma>)))"
        using 2 summable_mult by simp
      ultimately show ?thesis
        using summable_comparison_test' by fast
    qed
    then have summable_A: "summable (\<lambda>m. measure ?M(A (m + n)))" for n
      by (subst summable_iff_shift)
    then have lim_B: "(\<lambda>n. measure ?M (?B n)) \<longlonglongrightarrow> 0"
    proof -        
      have measure_B_le: "measure ?M (?B n) \<le> (\<Sum>m. measure ?M (A (m + n)))" for n
        apply (rule proc_source.finite_measure_subadditive_countably)
        using A_measurable summable_A by blast+
      have lim_A: "(\<lambda>n. (\<Sum>m. measure ?M (A (m + n)))) \<longlonglongrightarrow> 0"
        by (fact suminf_exist_split2[OF \<open>summable (\<lambda>m. measure ?M (A m))\<close>])
      have "convergent (\<lambda>n. measure ?M (?B n))"
        apply (intro Bseq_monoseq_convergent BseqI'[where K="measure ?M (\<Union> (range A))"])
        apply simp
         apply (meson A_measurable UNIV_I Union_mono image_iff image_subsetI proc_source.finite_measure_mono sets.countable_UN)
        apply (rule decseq_imp_monoseq)
        unfolding decseq_def
        using Union_add_subset proc_source.finite_measure_mono
        by (metis A_measurable countable_Un_Int(1))
      then obtain L where lim_B: "(\<lambda>n. measure ?M (?B n)) \<longlonglongrightarrow> L"
        unfolding convergent_def by auto
      then have "L \<ge> 0"
        by (simp add: LIMSEQ_le_const)
      moreover have "L \<le> 0"
        using measure_B_le by (simp add: LIMSEQ_le[OF lim_B lim_A])
      ultimately show ?thesis
        using lim_B by simp
    qed
    then have N_null: "?N \<in> null_sets ?M"
    proof -
      have "(\<lambda>n. measure ?M (?B n)) \<longlonglongrightarrow> measure ?M ?N"
        apply (rule proc_source.finite_Lim_measure_decseq)
          using A_measurable apply blast
          apply (intro monotoneI, simp add: Union_add_subset)
        done
      then have "measure ?M ?N = 0"
        using lim_B LIMSEQ_unique by blast
      then show ?thesis
        by (auto simp add: emeasure_eq_ennreal_measure)
    qed
    {
      fix \<omega> assume \<omega>: "\<omega> \<in> space ?M - ?N"
      then obtain n\<^sub>0 :: nat where n_zero: "\<omega> \<notin> (\<Union>n. A (n + n\<^sub>0))"
        by blast
      have nzero_ge: "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> 2^n * T \<ge> 1"
      proof (rule ccontr)
        fix n assume "n\<^sub>0 \<le> n" "\<not> 1 \<le> 2 ^ n * T"
        then have "A n = space ?M"
          unfolding A_def by simp
        then have "space ?M \<subseteq> (\<Union>m. A (m + n))"
          by (smt (verit, del_insts) UNIV_I UN_upper add_0)
        also have "(\<Union>m. A (m + n)) \<subseteq> (\<Union>m. A (m + n\<^sub>0))"
          by (simp add: Union_add_subset \<open>n\<^sub>0 \<le> n\<close>)
        finally show False
          using \<omega> n_zero by blast
      qed
      have omega_notin: "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> \<omega> \<notin> A n"
        by (metis n_zero UNIV_I UN_iff add.commute le_Suc_ex)
      then have X_dyadic_incr: "dist (X ((real_of_int k-1)/2^n) \<omega>) (X (real_of_int k/2^n) \<omega>) < 2 powr (- \<gamma> * n)"
        if "k \<in> {1..\<lfloor>2^n * T\<rfloor>}" "n \<ge> n\<^sub>0" for n k
      proof - (* TODO: clean this up *)
        have "finite {1..\<lfloor>2^n * T\<rfloor>}" "{1..\<lfloor>2^n * T\<rfloor>} \<noteq> {}"
          using that(2) nzero_ge by simp_all
        then have fin_nonempty: "finite {dist (X (real_of_int (k - 1) * 2 powr - real n) \<omega>) (X (real_of_int k * 2 powr - real n) \<omega>) |k.
                   k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}}" "{dist (X (real_of_int (k - 1) * 2 powr - real n) \<omega>) (X (real_of_int k * 2 powr - real n) \<omega>) |k.
                   k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}} \<noteq> {}"
          by fastforce+
        have "2 powr (- \<gamma> * real n)
           > Max {dist (X (real_of_int (k - 1) * 2 powr - real n) \<omega>) (X (real_of_int k * 2 powr - real n) \<omega>) |k.
                   k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}}"
          using omega_notin[OF that(2)] nzero_ge[OF that(2)] \<omega> unfolding A_def by auto
        then have "2 powr (- \<gamma> * real n) > dist (X (real_of_int (k - 1) * 2 powr - real n) \<omega>) (X (real_of_int k * 2 powr - real n) \<omega>)"
          using Max_less_iff[OF fin_nonempty] that(1) by blast
        then show ?thesis
          by (smt (verit, ccfv_SIG) divide_powr_uminus of_int_1 of_int_diff powr_realpow)
      qed

      text \<open> The objective of this block is to show that, for dyadic numbers s t with the same resolution:
     | X t \<omega> - x s \<omega> | \<le> 2 * 2 powr (- \<gamma> * n) / (1 - 2 powr - \<gamma>)
    Holder continuity on dyadic numbers follows directly from this fact.
  \<close>
  
      {
        fix m n :: nat assume mn: "m \<ge> n" "n \<ge> n\<^sub>0"
        fix s t :: real 
          assume s_dyadic: "s \<in> dyadic_interval_step m 0 T"
          and t_dyadic: "t \<in> dyadic_interval_step m 0 T"
          and st: "s \<le> t" "norm (s - t) \<le> 1/2^n"
        let ?u = "\<lfloor>2^n * s\<rfloor> / 2^n"
        have "?u = Max (dyadic_interval_step n 0 s)"
          apply (rule dyadic_interval_step_Max[symmetric])
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
          using X_dyadic_incr sorry
      } note dist_dyadic_fixed = this

      text \<open> We show that for dyadic rationals, X is Holder-continuous \<close>
      let ?C\<^sub>0 = "2 powr (1 + \<gamma>) / (1 - 2 powr - \<gamma>)"
      have "?C\<^sub>0 > 0"
        by (smt (verit) \<open>\<gamma> > 0\<close> \<open>\<gamma> < 1\<close> less_divide_eq_1_pos powr_eq_one_iff powr_ge_pzero powr_le_cancel_iff)
      {
        fix s t
        assume s: "s \<in> (\<Union>n. dyadic_interval_step n 0 T)"
           and t: "t \<in> (\<Union>n. dyadic_interval_step n 0 T)"
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
          using dist_dyadic_fixed sorry
      } note dist_dyadic = this
      let ?K = "\<lambda>t s. ?C\<^sub>0 * 2 powr ((1-\<gamma>) * n\<^sub>0) * (dist t s) powr \<gamma>"
      have X_incr: "dist (X t \<omega>) (X s \<omega>) \<le> ?K t s"
        if "s \<in> (\<Union>n. dyadic_interval_step n 0 T)" and "t \<in> (dyadic_interval 0 T)"
        for s t
        using dist_dyadic sorry
      then have holder_dyadic: "\<gamma>-holder_on (dyadic_interval 0 T) (\<lambda>t. X t \<omega>)"
        apply (intro holder_onI)
        using \<open>\<gamma> \<in> {0<..1}\<close> apply argo
        apply (intro exI[where x="?C\<^sub>0 * 2 powr ((1-\<gamma>) * n\<^sub>0)"])
        using \<open>?C\<^sub>0 > 0\<close> unfolding dyadic_interval_def
          apply (auto simp: \<open>?C\<^sub>0 > 0\<close> zero_less_divide_iff)
        done
      then have "uniformly_continuous_on (dyadic_interval 0 T) (\<lambda>t. X t \<omega>)"
        by (fact holder_uniform_continuous)
      then have "\<exists>L. ((\<lambda>s. X s \<omega>) \<longlongrightarrow> L) (at t within (dyadic_interval 0 T))"
        if "t \<in> {0..T} - (dyadic_interval 0 T)" for t
        apply (rule uniformly_continuous_on_extension_at_closure[where x = t])
        using that dyadic_interval_dense apply fast
        apply fast
        done
      define L where
          "L \<equiv> (\<lambda>t. (THE L. ((\<lambda>s. X s \<omega>) \<longlongrightarrow> L) (at t within (\<Union>n. dyadic_interval_step n 0 T))))"
      define X_tilde :: "real \<Rightarrow> 'b" where
        "X_tilde \<equiv> \<lambda>t. if t \<in> (\<Union>n. dyadic_interval_step n 0 T) then X t \<omega> else L t"
      then have "dist (X_tilde s) (X_tilde t) \<le> ?K s t" if "s \<in> {0..T}" "t \<in> {0..T}" for s t
        sorry text \<open> Should be analogous to the proof of @{thm dist_dyadic} \<close>
      then have "\<gamma>-holder_on {0..T} X_tilde"
        apply (intro holder_onI)
        using \<open>\<gamma> \<in> {0<..1}\<close> apply argo
        apply (intro exI[where x="?C\<^sub>0 * 2 powr ((1-\<gamma>) * n\<^sub>0)"])
        using \<open>?C\<^sub>0 > 0\<close> apply (auto simp: \<open>?C\<^sub>0 > 0\<close>zero_less_divide_iff)
        done
      then have "local_holder_on \<gamma> {0..T} X_tilde"
        using holder_implies_local_holder by blast
    } note X_tilde_arb_omega = this (* GIVE BETTER NAME *)
    define default :: 'b where "default = (SOME x. True)"
    define X_tilde :: "real \<Rightarrow> 'a \<Rightarrow> 'b" where
    "X_tilde \<equiv> (\<lambda>t \<omega>. if \<omega> \<in> ?N then default else
                      (if t \<in> (\<Union>n. dyadic_interval_step n 0 T) then X t \<omega>
               else THE L. ((\<lambda>s. X s \<omega>) \<longlongrightarrow> L) (at t within (\<Union>n. dyadic_interval_step n 0 T))))"
    have local_holder_X_tilde: "local_holder_on \<gamma> {0..T} (\<lambda>t. X_tilde t \<omega>)" if "\<omega> \<in> space ?M" for \<omega>
    proof (cases "\<omega> \<in> ?N")
      case True
      then show ?thesis
        unfolding X_tilde_def using local_holder_const \<open>0 < \<gamma>\<close> \<open>\<gamma> < 1\<close> by fastforce
    next
      case False
      then have 1: "\<omega> \<in> space ?M - ?N"
        using that by blast
      show ?thesis
        unfolding X_tilde_def by (simp only: False if_False X_tilde_arb_omega[OF 1])
    qed
    have "AE \<omega> in ?M. X t \<omega> = X_tilde t \<omega>" if "t \<in> {0..T}" for t
    proof (cases "t \<in> (\<Union>n. dyadic_interval_step n 0 T)")
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
         apply (metis random_process target_borel)
        defer
      using sets.sets_Collect_const apply blast
       apply auto[1]
      find_theorems tendsto borel
      sorry (* Prove limit is measurable *)
    ultimately have "modification (restrict_index X {0..T}) (process_of ?M (proc_target X) {0..T} X_tilde default)"
      apply (intro modificationI)
      unfolding compatible_def apply safe
           apply (simp_all add: proc_source.prob_space_axioms)
      by (metis restrict_index_source)
    then have "\<exists>Y. modification (restrict_index X {0..T}) Y \<and> (\<forall>x \<in> space ?M. local_holder_on \<gamma> {0..T} (\<lambda>t. process Y t x))"
      apply (intro exI[where x="(process_of ?M (proc_target X) {0..T} X_tilde default)"])
      apply safe
      apply (subst process_process_of)
         apply (simp_all add: proc_source.prob_space_axioms X_tilde_measurable)
      using local_holder_X_tilde unfolding local_holder_on_def by auto
  } note * = this
  define Mod where "Mod \<equiv> \<lambda>T. SOME Y. modification (restrict_index X {0..T}) Y \<and> 
    (\<forall>x\<in>space ?M. local_holder_on \<gamma> {0..T} (\<lambda>t. Y t x))"
  have Mod: "modification (restrict_index X {0..T}) (Mod T)"
    "(\<forall>x\<in>space ?M. local_holder_on \<gamma> {0..T} (\<lambda>t. (Mod T) t x)) " if "0 < T" for T
    using someI_ex[OF *[OF that]] unfolding Mod_def by linarith+
  then have compatible_Mod: "compatible (restrict_index X {0..T}) (Mod T)" if "0 < T" for T
    using that modificationD(1) by blast
  then have Mod_source[simp]: "proc_source (Mod T) = ?M"  if "0 < T" for T
    by (metis compatible_source restrict_index_source that)
  have Mod_target: "sets (proc_target (Mod T)) = sets (proc_target X)"  if "0 < T" for T
    by (metis compatible_Mod[OF that] compatible_target restrict_index_target)
  have indistinguishable_mod: 
    "indistinguishable (restrict_index (Mod S) {0..min S T}) (restrict_index (Mod T) {0..min S T})"
    if "S > 0" "T > 0" for S T
  proof -
    have *: "modification (restrict_index (Mod S) {0..min S T}) (restrict_index (Mod T) {0..min S T})"
    proof -
      have "modification (restrict_index X {0..min S T}) (restrict_index (Mod S) {0..min S T})"
        using restrict_index_override modification_restrict_index Mod[OF that(1)] by fastforce
      moreover have "modification (restrict_index X {0..min S T}) (restrict_index (Mod T) {0..min S T})"
        using restrict_index_override modification_restrict_index Mod[OF that(2)] by fastforce
      ultimately show ?thesis
        using modification_sym modification_trans by blast
    qed
    then show ?thesis
      apply (rule modification_continuous_indistinguishable)
    proof (goal_cases _ continuous_S continuous_T)
     show "\<exists>Ta>0. proc_index (restrict_index (Mod S) {0..min S T}) = {0..Ta}"
        by (metis that min_def restrict_index_index)
    next
      case (continuous_S)
      have "\<forall>x \<in> space ?M. continuous_on {0..S} (\<lambda>t. (Mod S) t x)"
        using Mod[OF that(1)] local_holder_continuous by blast
      then have "\<forall>x \<in> space ?M. continuous_on {0..min S T} (\<lambda>t. (Mod S) t x)"
        using continuous_on_subset by fastforce
      then show ?case
        by (auto simp: that(1))
    next
      case (continuous_T)
      have "\<forall>x \<in> space ?M. continuous_on {0..T} (\<lambda>t. (Mod T) t x)"
        using Mod[OF that(2)] local_holder_continuous by fast
      then have 2: "\<forall>x \<in> space ?M. continuous_on {0..min S T} (\<lambda>t. (Mod T) t x)"
        using continuous_on_subset by fastforce
      then show ?case
        by (auto simp: that(2))
    qed
  qed
  have "\<forall>S > 0. \<forall>T > 0. \<exists>N. N \<in> null_sets ?M \<and> {\<omega> \<in> space ?M. \<exists>t \<in> {0..min S T}.
   (Mod S) t \<omega> \<noteq> (Mod T) t \<omega>} \<subseteq> N"
    apply (fold Bex_def)
    using indistinguishable_mod[THEN indistinguishable_null_ex] by simp
  then obtain N where N: "N S T \<in> null_sets ?M"
    "{\<omega> \<in> space ?M. \<exists>t \<in> {0..min S T}. (Mod S) t \<omega> \<noteq> (Mod T) t \<omega>} \<subseteq> N S T" 
  if "S > 0" "T > 0" for S T
    apply (simp add: choice_iff' that)
    apply (erule exE)
    apply blast
    done
  define N_inf where "N_inf \<equiv> (\<Union>S \<in> \<nat> - {0}. (\<Union> T \<in> \<nat> - {0}. N S T))"
  from N have "N_inf \<in> null_sets ?M"
    unfolding N_inf_def
    apply (intro null_sets_UN')
     apply (rule countable_Diff)
      apply (simp add: Nats_def)+
    by force
  have Mod_eq_N_inf: "(Mod S) t \<omega> = (Mod T) t \<omega>"
    if "\<omega> \<in> space ?M - N_inf" "t \<in> {0..min S T}" "S \<in> \<nat> - {0}" "T \<in> \<nat> - {0}" for \<omega> t S T
  proof -
    have "\<omega> \<in> space ?M - N S T"
      using that(1,3,4) unfolding N_inf_def by blast
    moreover have "S > 0" "T > 0"
      using that(2,3,4) by auto
    ultimately have "\<omega> \<in> {\<omega> \<in> space ?M. \<forall>t \<in>{0..min S T}. (Mod S) t \<omega> = (Mod T) t \<omega>}"
      using N(2) by auto
    then show ?thesis
      using that(2) by blast
  qed
  define default :: 'b where "default = (SOME x. True)"
  define X_mod where "X_mod \<equiv> \<lambda>t \<omega>. if \<omega> \<in> space ?M - N_inf then (Mod \<lfloor>t+1\<rfloor>) t \<omega> else default"
  have Mod_measurable[measurable]: "\<forall>t\<in>{0..}. X_mod t \<in> ?M \<rightarrow>\<^sub>M proc_target X"
  proof (intro ballI)
    fix t :: real assume "t \<in> {0..}"
    then have "0 < \<lfloor>t + 1\<rfloor>"
      by force
    then show "X_mod t \<in> ?M \<rightarrow>\<^sub>M proc_target X"
      unfolding X_mod_def apply measurable
        apply (subst measurable_cong_sets[where M'= "proc_source (Mod \<lfloor>t + 1\<rfloor>)" and N' = "proc_target (Mod \<lfloor>t + 1\<rfloor>)"])
      using Mod_source \<open>0 < \<lfloor>t + 1\<rfloor>\<close> apply presburger
      using Mod_target \<open>0 < \<lfloor>t + 1\<rfloor>\<close> apply presburger
        apply (meson random_process)
      apply simp
      apply (metis \<open>N_inf \<in> null_sets ?M\<close> Int_def null_setsD2 sets.Int_space_eq1 sets.compl_sets)
      done
  qed
  have "modification X (process_of ?M (proc_target X) {0..} X_mod default)"
  proof (intro modificationI ballI)
    show "compatible X (process_of ?M (proc_target X) {0..} X_mod default)"
      apply (intro compatibleI)
        apply (subst source_process_of)
           prefer 5 apply (subst target_process_of)
      using Mod_measurable proc_source.prob_space_axioms apply auto
      done
    fix t assume "t \<in> proc_index X"
    then have "t \<in> {0..}"
      by simp
    then have "real_of_int \<lfloor>t\<rfloor> + 1 > 0"
      by (simp add: add.commute add_pos_nonneg)
    then have "\<exists>N \<in> null_sets ?M. \<forall>\<omega> \<in> space ?M - N. 
        X t \<omega> = (process_of ?M (proc_target X) {0..} X_mod default) t \<omega>"
    proof -
      have 1: "(process_of ?M (proc_target X) {0..} X_mod default) t \<omega> = (Mod (real_of_int \<lfloor>t\<rfloor> + 1)) t \<omega>"
          if "\<omega> \<in> space ?M - N_inf" for \<omega>
        apply (subst process_process_of)
        using Mod_measurable proc_source.prob_space_axioms apply auto
        unfolding X_mod_def using that apply simp
        using \<open>t \<in> {0..}\<close> apply simp
        done
      have "\<exists>N \<in> null_sets ?M. \<forall>\<omega> \<in> space ?M - N. X t \<omega> = (Mod (real_of_int \<lfloor>t\<rfloor> + 1)) t \<omega>"
      proof -
        obtain N where "{x \<in> space ?M. (restrict_index X {0..real_of_int \<lfloor>t\<rfloor> + 1}) t x \<noteq> (Mod (real_of_int \<lfloor>t\<rfloor> + 1)) t x} \<subseteq> N \<and>
      N \<in> null_sets (proc_source (restrict_index X {0..(real_of_int \<lfloor>t\<rfloor> + 1)}))"
          using Mod(1)[OF \<open>real_of_int \<lfloor>t\<rfloor> + 1 > 0\<close>, THEN modification_null_set, of t]
          using \<open>t \<in> {0..}\<close> by auto
        then show ?thesis
          by (smt (verit, ccfv_threshold) DiffE mem_Collect_eq restrict_index_process restrict_index_source subset_eq)
      qed
      then obtain N where "N \<in> null_sets ?M" "\<forall>\<omega> \<in> space ?M - N. X t \<omega> = (Mod (real_of_int \<lfloor>t\<rfloor> + 1)) t \<omega>"
        by blast
      then show ?thesis
        apply (intro bexI[where x="N \<union> N_inf"])
         apply (metis "1" DiffE DiffI UnCI)
        using \<open>N_inf \<in> null_sets ?M\<close> by blast
    qed
    then show "AE x in ?M. X t x = (process_of ?M (proc_target X) {0..} X_mod default) t x"
      by (smt (verit, del_insts) DiffI eventually_ae_filter mem_Collect_eq subsetI)
  qed

  text \<open> Because the processes are indistinguishable, they are all equal on \<omega>, so the local holder
  continuity extends to {0..}. \<close>
  moreover have "local_holder_on \<gamma> {0..} (\<lambda>t. X_mod t \<omega>)" for \<omega>
  proof (cases "\<omega> \<in> space ?M - N_inf")
    case False
    then show ?thesis
     apply (simp only: X_mod_def)
      apply (metis local_holder_const \<open>\<gamma> \<in> {0<..1}\<close>)
      done
  next
    case True
    then have \<omega>: "\<omega> \<in> space ?M" "\<omega> \<notin> N_inf"
      by simp_all
    then show ?thesis
    proof (intro local_holder_ballI[OF \<open>\<gamma> \<in> {0<..1}\<close>] ballI)
      fix t::real assume "t \<in> {0..}"
      then have "real_of_int \<lfloor>t\<rfloor> + 1 > 0"
        using floor_le_iff by force
      have "t < real_of_int \<lfloor>t\<rfloor> + 1"
        by simp
      then have "local_holder_on \<gamma> {0..real_of_int \<lfloor>t\<rfloor> + 1} (\<lambda>s. Mod (real_of_int \<lfloor>t\<rfloor> + 1) s \<omega>)"
        using Mod(2) \<omega>(1) \<open>real_of_int \<lfloor>t\<rfloor> + 1 > 0\<close> by blast
      then obtain \<epsilon> C where eC: "\<epsilon> > 0" "C \<ge> 0" "\<And>r s. r \<in> ball t \<epsilon> \<inter> {0..real_of_int \<lfloor>t\<rfloor> + 1} \<Longrightarrow>
         s \<in> ball t \<epsilon> \<inter> {0..real_of_int \<lfloor>t\<rfloor> + 1} \<Longrightarrow>
         dist (Mod (real_of_int \<lfloor>t\<rfloor> + 1) r \<omega>) (Mod (real_of_int \<lfloor>t\<rfloor> + 1) s \<omega>) \<le> C * dist r s powr \<gamma>"
        apply -
        apply (erule local_holder_onE)
          apply (rule \<open>\<gamma> \<in> {0<..1}\<close>)
        using \<open>t \<in> {0..}\<close> \<open>t < real_of_int \<lfloor>t\<rfloor> + 1\<close> apply fastforce
        apply blast
        done
      define \<epsilon>' where "\<epsilon>' = min \<epsilon> (if frac t = 0 then 1/2 else 1 - frac t)"
      have e': "\<epsilon>' \<le> \<epsilon> \<and> \<epsilon>' > 0 \<and> ball t \<epsilon>' \<inter> {0..} \<subseteq> {0..real_of_int \<lfloor>t\<rfloor> + 1}"
        unfolding \<epsilon>'_def
        apply (auto simp: eC(1) dist_real_def frac_lt_1)
          apply argo
        apply (simp add: frac_floor)
        done
      {
        fix r s
        assume r:  "r \<in> ball t \<epsilon>' \<inter> {0..}"
        assume s:  "s \<in> ball t \<epsilon>' \<inter> {0..}"

        then have rs_ball: "r \<in> ball t \<epsilon> \<inter> {0..real_of_int \<lfloor>t\<rfloor> + 1}"
                           "s \<in> ball t \<epsilon> \<inter> {0..real_of_int \<lfloor>t\<rfloor> + 1}"
          using e' r s by auto
        then have "r \<in> {0..min (real_of_int \<lfloor>t\<rfloor> + 1) (real_of_int \<lfloor>r + 1\<rfloor>)}"
           by auto
        then have "(Mod (real_of_int \<lfloor>t\<rfloor> + 1)) r \<omega> = X_mod r \<omega>"
          unfolding X_mod_def apply (simp only: True if_True)
          apply (intro Mod_eq_N_inf[OF True])
            apply simp
            using \<open>t \<in> {0..}\<close> apply auto
             apply (metis (no_types, opaque_lifting)floor_in_Nats Nats_1 Nats_add Nats_cases 
                    of_int_of_nat_eq of_nat_in_Nats, linarith)+
          done
        moreover have "(Mod (real_of_int \<lfloor>t\<rfloor> + 1)) s \<omega> = X_mod s \<omega>"
          unfolding X_mod_def apply (simp only: True if_True)
          apply (intro Mod_eq_N_inf[OF True])
          using \<open>s \<in> ball t \<epsilon> \<inter> {0..real_of_int \<lfloor>t\<rfloor> + 1}\<close> apply simp
            apply simp
          using \<open>t \<in> {0..}\<close> apply auto
          apply (metis (no_types, opaque_lifting)floor_in_Nats Nats_1 Nats_add Nats_cases of_int_of_nat_eq of_nat_in_Nats)
            apply linarith
           apply (smt (verit) Int_iff Nats_1 Nats_add Nats_altdef1 atLeast_iff mem_Collect_eq s zero_le_floor)
          apply (metis s Int_iff atLeast_iff linorder_not_le real_of_int_floor_add_one_gt)
          done
        ultimately have "dist (X_mod r \<omega>) (X_mod s \<omega>) \<le> C * dist r s powr \<gamma>"
          using eC(3)[OF rs_ball] by simp
      }
      then show "\<exists>\<epsilon>>0. \<exists>C\<ge>0. \<forall>r\<in>ball t \<epsilon> \<inter> {0..}. \<forall>s\<in>ball t \<epsilon> \<inter> {0..}. dist (X_mod r \<omega>) (X_mod s \<omega>) \<le> C * dist r s powr \<gamma>"
        using e' eC(2) by blast
    qed
  qed

  ultimately show ?thesis
    apply (intro exI[where x="process_of ?M (proc_target X) {0..} (X_mod) default"])
    apply simp
    apply (intro ballI)
    apply (subst process_process_of)
    using \<open>\<forall>t\<in>{0..}. X_mod t \<in> ?M \<rightarrow>\<^sub>M proc_target X\<close> apply simp
    using proc_source.prob_space_axioms apply blast
     apply simp
    by (smt (verit) local_holder_on_cong)
qed

end
