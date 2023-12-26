theory Continuous_Modification
  imports Stochastic_Process Holder_Continuous Dyadic_Interval Measure_Convergence
begin

text \<open> Klenke 5.11: Markov inequality. Compare with @{thm nn_integral_Markov_inequality} \<close>

text_raw \<open>\DefineSnippet{nn_integral_Markov_inequality_extended}{\<close>
lemma nn_integral_Markov_inequality_extended:
  fixes f :: "real \<Rightarrow> ennreal" and \<epsilon> :: real and X :: "'a \<Rightarrow> real"
  assumes mono: "mono_on (range X \<union> {0<..}) f"
      and finite: "\<And>x. f x < \<infinity>"
      and e: "\<epsilon> > 0" "f \<epsilon> > 0"
      and [measurable]: "X \<in> borel_measurable M"
    shows "emeasure M {p \<in> space M. (X p) \<ge> \<epsilon>} \<le> (\<integral>\<^sup>+ x. f (X x) \<partial>M) / f \<epsilon>"
text_raw \<open>}%EndSnippet\<close>
proof -
  have f_eq: "f = (\<lambda>x. ennreal (enn2real (f x)))"
    using finite by simp
  have "mono_on (range X) (\<lambda>x. enn2real (f x))"
    apply (intro mono_onI)
    using mono[THEN mono_onD] finite by (simp add: enn2real_mono)
  then have "f \<in> borel_measurable (restrict_space borel (range X))"
    apply (subst f_eq)
    apply (intro measurable_compose[where f="\<lambda>x. enn2real (f x)" and g=ennreal])
    using borel_measurable_mono_on_fnc apply blast
    apply simp
    done
  then have "(\<lambda>x. f (X x)) \<in> borel_measurable M"
    apply (intro measurable_compose[where g=f and f=X and N="restrict_space borel (range X)"])
    apply (simp_all add: measurable_restrict_space2)
    done
  then have "{x \<in> space M. f (X x) \<ge> f \<epsilon>} \<in> sets M"
    by measurable
  then have "f \<epsilon> * emeasure M {x \<in> space M. X x \<ge> \<epsilon>} \<le> \<integral>\<^sup>+x\<in>{x \<in> space M. f \<epsilon> \<le> f (X x)}. f \<epsilon> \<partial>M"
    apply (simp add: nn_integral_cmult_indicator)
    using e mono_onD[OF mono] zero_le apply (blast intro: mult_left_mono emeasure_mono)
    done
  also have "... \<le> \<integral>\<^sup>+x\<in>{x \<in> space M. f \<epsilon> \<le> f (X x)}. f (X x) \<partial>M"
    apply (rule nn_integral_mono)
    subgoal for x
      apply (cases "f \<epsilon> \<le> f (X x)")
      using ennreal_leI by auto
    done
  also have "... \<le> \<integral>\<^sup>+ x. f (X x) \<partial>M"
    by (simp add: nn_integral_mono indicator_def)
  finally have "emeasure M {p \<in> space M. \<epsilon> \<le> X p} * f \<epsilon> / f \<epsilon> \<le> (\<integral>\<^sup>+ x. f (X x) \<partial>M) / f \<epsilon>"
    by (simp add: divide_right_mono_ennreal field_simps)
  then show ?thesis
    using mult_divide_eq_ennreal finite[of "\<epsilon>"] e(2) by simp
qed

lemma nn_integral_Markov_inequality_extended_rnv:
  fixes f :: "real \<Rightarrow> real" and \<epsilon> :: real and X :: "'a \<Rightarrow> 'b :: real_normed_vector"
  assumes [measurable]: "X \<in> borel_measurable M"
      and mono: "mono_on {0..} f"
      and e: "\<epsilon> > 0" "f \<epsilon> > 0"
    shows "emeasure M {p \<in> space M. norm (X p) \<ge> \<epsilon>} \<le> (\<integral>\<^sup>+ x. f (norm (X x)) \<partial>M) / f \<epsilon>"
  apply (rule nn_integral_Markov_inequality_extended)
    using mono ennreal_leI unfolding mono_on_def apply force
    apply (simp_all add: e)
    done

lemma (in prob_space) tendsto_prob_eq_limit_AE:
  fixes X :: "real \<Rightarrow> 'a \<Rightarrow> 'b :: {second_countable_topology,metric_space}"
  assumes [measurable]: "\<And>i. X i \<in> borel_measurable M" "l \<in> borel_measurable M"
  assumes t: "t \<in> {0..T}" "T \<noteq> 0"
  assumes conv: "tendsto_measure M X l (at t within {0..})"
  assumes lim: "\<And>x. ((\<lambda>s. X s x) \<longlongrightarrow> (l x))(at t within dyadic_interval 0 T)"
  shows "AE x in M. X t x = l x"
proof -
  from lim have "tendsto_measure M X l (at t within dyadic_interval 0 T)"
    using Lim_measure_pointwise assms(1) assms(2) by blast
  moreover from conv have "tendsto_measure M X l (at t within {0..T})"
    by (metis tendsto_measure_mono Icc_subset_Ici_iff at_le dual_order.refl)
  thm LIMSEQ_measure_unique_AE
  ultimately show ?thesis sorry
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

lemma borel_measurable_at_within [measurable]:
  assumes "\<And>t. t \<in> T \<Longrightarrow> f t \<in> borel_measurable M"
  shows "(\<lambda>\<omega>. Lim (at x within T) (\<lambda>t. f t \<omega>)) \<in> borel_measurable M"
  apply (simp add: t2_space_class.Lim_def)
  find_theorems Lim measurable
  thm borel_measurable_lim
  thm convergent_limsup_cl
  thm Liminf_def
  find_theorems Limsup Lim
  thm lim_imp_Limsup
  sorry

text \<open> Klenke 21.6 - Kolmorogov-Chentsov\<close>

locale Kolmogorov_Chentsov = 
  fixes X :: "(real, 'a, 'b :: polish_space) stochastic_process"
    and a b C \<gamma> :: real
  assumes index[simp]: "proc_index X = {0..}"
      and target_borel[simp]: "proc_target X = borel"
      and gt_0: "a > 0" "b > 0" "C > 0"
      and b_leq_a: "b \<le> a" (* Probably follows from other assms *)
      and gamma: "\<gamma> \<in> {0<..<b/a}"
      and expectation: "\<And>s t. \<lbrakk>s \<ge> 0; t \<ge> 0\<rbrakk> \<Longrightarrow>
          (\<integral>\<^sup>+ x. dist (X t x) (X s x) powr a \<partial>proc_source X) \<le> C * dist t s powr (1+b)"
begin

lemma gamma_0_1[simp]:"\<gamma> \<in> {0<..1}"
  using gt_0 b_leq_a gamma
  by (metis divide_less_eq_1_pos divide_self greaterThanAtMost_iff 
          greaterThanLessThan_iff nless_le order_less_trans)

lemma gamma_gt_0[simp]: "\<gamma> > 0"
  using gamma greaterThanLessThan_iff by blast

lemma gamma_le_1[simp]: "\<gamma> \<le> 1"
  using gamma_0_1 by auto

abbreviation "source \<equiv> proc_source X"

lemma X_borel_measurable[measurable]: "X t \<in> borel_measurable source" for t
    by (metis random_process target_borel)

lemma markov: "\<P>(x in source. \<epsilon> \<le> dist (X t x) (X s x)) \<le> (C * dist t s powr (1 + b)) / \<epsilon> powr a"
    if "s \<ge> 0" "t \<ge> 0" "\<epsilon> > 0" for s t \<epsilon>
proof -
  let ?inc = "\<lambda>x. dist (X t x) (X s x) powr a"
  have "emeasure source {x \<in> space source. \<epsilon> \<le> dist (X t x) (X s x)}
   \<le> integral\<^sup>N source ?inc / \<epsilon> powr a"
    apply (rule nn_integral_Markov_inequality_extended)
    using that(1,2) apply measurable
    using gt_0(1) imageE powr_mono2 apply (auto intro: mono_onI)[1]
    using that apply simp_all
    done
  also have "... \<le> (C * dist t s powr (1 + b)) / ennreal (\<epsilon> powr a)"
    apply (rule divide_right_mono_ennreal)
    using expectation[OF that(1,2)] ennreal_leI by simp
  finally have "emeasure source {x \<in> space source. \<epsilon> \<le> dist (X t x) (X s x)}
     \<le> (C * dist t s powr (1 + b)) / \<epsilon> powr a"
    using that(3) divide_ennreal gt_0(3) by simp
  moreover have "C * dist t s powr (1 + b) / \<epsilon> powr a \<ge> 0"
    using gt_0(3) by auto
  ultimately show ?thesis
    by (simp add: proc_source.emeasure_eq_measure)
qed

lemma conv_in_prob:
  assumes "t \<ge> 0"
  shows "tendsto_measure (proc_source X) X (X t) (at t within {0..})"
proof (simp add: finite_measure.tendsto_measure_finite_leq, safe, intro Lim_withinI)
  fix p \<epsilon> :: real assume "0 < p" "0 < \<epsilon>"
  let ?q = "(p * \<epsilon> powr a / C) powr (1/(1+b))"
  have "0 < ?q"
    using \<open>0 < p\<close> gt_0(3) \<open>0 < \<epsilon>\<close> by simp
  have p_eq: "p = (C * ?q powr (1 + b)) / \<epsilon> powr a"
    using gt_0 \<open>0 < ?q\<close> \<open>0 < p\<close> by (simp add: field_simps powr_powr)
  have "0 < dist r t \<and> dist r t < ?q \<longrightarrow> dist \<P>(x in source. \<epsilon> \<le> dist (X t x) (X r x)) 0 \<le> p"
    if "r \<in> {0..}" for r
  proof (clarsimp)
    assume "r \<noteq> t" "dist r t < ?q"
    have "0 \<le> r"
      using that by auto
    from \<open>dist r t < ?q\<close> have "C * dist r t powr (1 + b) / \<epsilon> powr a \<le> p"
      apply (subst p_eq)
      using gt_0(2) gt_0(3) apply (simp add: divide_le_cancel powr_mono2)
      done
    then show "\<P>(x in source. \<epsilon> \<le> dist (X t x) (X r x)) \<le> p"
      using markov[OF \<open>0 \<le> r\<close> assms \<open>0 < \<epsilon>\<close>] by (simp add: dist_commute)
  qed
  then show "\<exists>d>0. \<forall>r\<in>{0..}. 0 < dist r t \<and> dist r t < d \<longrightarrow> dist \<P>(x in source. \<epsilon> \<le> dist (X r x) (X t x)) 0 \<le> p"
    apply (intro exI[where x="?q"])
    apply (subst(3) dist_commute)
    using \<open>0 < p\<close> gt_0(3) \<open>0 < \<epsilon>\<close> dist_commute by fastforce
qed

lemma incr: "\<P>(x in source. 2 powr (- \<gamma> * n) \<le> dist (X ((k - 1) * 2 powr - n) x) (X (k * 2 powr - n) x))
         \<le> C * 2 powr (-n * (1+b-a*\<gamma>))"
    if "\<gamma> > 0" "k \<ge> 1" "n \<ge> 0" for k n
proof -
  have "\<P>(x in source. 2 powr (- \<gamma> * n) \<le> dist (X ((k - 1) * 2 powr - n) x) (X (k * 2 powr - n) x))
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

end

locale Kolmogorov_Chentsov_finite = Kolmogorov_Chentsov +
  fixes T :: real
  assumes zero_le_T: "0 < T"
begin

definition "A \<equiv> \<lambda>n. if 2 ^ n * T < 1 then space source else 
  {x \<in> space source. 
    Max {dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x)
       | k. k \<in> {1..\<lfloor>2^n * T\<rfloor>}} \<ge> 2 powr (-\<gamma> * real n)}"

abbreviation "B \<equiv> \<lambda>n. (\<Union>m. A (m + n))"

abbreviation "N \<equiv> \<Inter>(range B)"

lemma A_geq: "2 ^ n * T \<ge> 1 \<Longrightarrow> A n = {x \<in> space source. 
    Max {dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x)
   | k. k \<in> {1..\<lfloor>2^n * T\<rfloor>}} \<ge> 2 powr (-\<gamma> * real n)}" for n
  by (simp add: A_def)

lemma A_measurable[measurable]: "A n \<in> sets source"
  unfolding A_def apply (cases "2 ^ n * T < 1")
   apply simp
   apply (simp only: if_False)
   apply measurable
  done

lemma emeasure_A_leq:
  fixes n :: nat
  assumes [simp]: "2^n * T \<ge> 1"
  shows "emeasure source (A n) \<le> C * T * 2 powr (- n * (b - a * \<gamma>))"
proof -
  have nonempty: "{1..\<lfloor>2^n * T\<rfloor>} \<noteq> {}"
      using assms by fastforce
    have finite: "finite {1..\<lfloor>2^n * T\<rfloor>}"
      by simp
    have "emeasure source (A n) \<le> emeasure source (\<Union>k \<in> {1..\<lfloor>2^n * T\<rfloor>}.
    {x\<in>space source. dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x) \<ge> 2 powr (- \<gamma> * real n)})"
    (is "emeasure source (A n) \<le> emeasure source ?R")
    proof (rule emeasure_mono, intro subsetI)
      fix x assume *: "x \<in> A n"
      from * have in_space: "x \<in> space source"
        using A_measurable sets.sets_into_space by blast
      from * have "2 powr (- \<gamma> * real n) \<le> Max {dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x) |k. k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}}"
        using A_geq assms by blast
      then have "\<exists>k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}. 2 powr (- \<gamma> * real n) \<le> dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x)"
        apply (simp only: setcompr_eq_image)
        apply (rule Max_finite_image_ex[where P="\<lambda>x. 2 powr (- \<gamma> * real n) \<le> x", OF finite nonempty])
        apply (metis Collect_mem_eq)
        done
      then show "x \<in> ?R"
        using in_space by simp
    next
      show "?R \<in> sets source"
        by measurable
    qed
    also have "... \<le> (\<Sum>k\<in>{1..\<lfloor>2^n * T\<rfloor>}. emeasure source 
  {x\<in>space source. dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x) \<ge> 2 powr (- \<gamma> * real n)})"
      apply (rule emeasure_subadditive_finite)
       apply blast
      apply (subst image_subset_iff)
      apply (intro ballI)
      apply measurable
      done
    also have "... \<le> C * 2 powr (- n * (1 + b - a * \<gamma>)) * (card {1..\<lfloor>2 ^ n * T\<rfloor>})"
    proof -
      {
        fix k assume "k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}"
        then have "real_of_int k \<ge> 1"
          by presburger
        then have "\<P>(x in source. 2 powr (- \<gamma> * real n) \<le> dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x))
               \<le> C * 2 powr (-(real n) * (1+b-a*\<gamma>))"
          using incr gamma by force
      } note X = this
      then have "sum (\<lambda>k. \<P>(x in source. 2 powr (- \<gamma> * real n) \<le> dist (X (real_of_int (k - 1) * 2 powr - real n) x) (X (real_of_int k * 2 powr - real n) x))) 
                      {1..\<lfloor>2 ^ n * T\<rfloor>} \<le> of_nat (card {1..\<lfloor>2 ^ n * T\<rfloor>}) * (C * 2 powr (-(real n) * (1+b-a*\<gamma>)))"
        by (fact sum_bounded_above)
      then show ?thesis
        using ennreal_leI by (auto simp: proc_source.emeasure_eq_measure mult.commute)
      qed
    also have "... \<le> C * 2 powr (- n * (1 + b - a * \<gamma>)) * \<lfloor>2 ^ n * T\<rfloor>"
      using nonempty zle_iff_zadd by force
    also have "... \<le> C * 2 powr (- n * (1+b - a * \<gamma>)) * 2^n * T"
      by (simp add:ennreal_leI gt_0(3))
    also have "... = C * 1/(2^n) * 2 powr (- n * (b - a * \<gamma>)) * 2^n * T"
      apply (intro ennreal_cong)
      apply (simp add: scale_left_imp_eq field_simps)
      by (smt (verit) powr_add powr_realpow)
    also have "... = C * T * 2 powr (- n * (b - a * \<gamma>))"
      by (simp add: field_simps)
    finally show ?thesis .
qed

lemma measure_A_leq: 
  assumes "2^n * T \<ge> 1"
  shows "measure source (A n) \<le> C * T * 2 powr (- n * (b - a * \<gamma>))"
  apply (intro measure_leq_emeasure_ennreal)
    using gt_0(3) zero_le_T apply auto[1]
    using emeasure_A_leq apply (simp add: A_geq assms)
    done

lemma summable_A: "summable (\<lambda>m. measure source (A m))"
proof -
  have "b - a * \<gamma> > 0"
    by (metis diff_gt_0_iff_gt gamma greaterThanLessThan_iff gt_0(1) mult.commute pos_less_divide_eq)
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
  from zero_le_T obtain N where "2^N * T \<ge> 1"
    by (metis dual_order.order_iff_strict mult.commute one_less_numeral_iff pos_divide_le_eq
        power_one_over reals_power_lt_ex semiring_norm(76) zero_less_numeral zero_less_power)
  then have "\<And>n. n \<ge> N \<Longrightarrow> 2^n * T \<ge> 1" 
    by (smt (verit, best) \<open>0 < T\<close> mult_right_mono power_increasing_iff)
  then have "\<And>n. n \<ge> N \<Longrightarrow> norm (measure source (A n)) \<le> C * T * 2 powr (- n * (b - a * \<gamma>))"
    using measure_A_leq by simp
  moreover have "summable (\<lambda>n. C * T * 2 powr (- n * (b - a * \<gamma>)))"
    using 2 summable_mult by simp
  ultimately show ?thesis
    using summable_comparison_test' by fast
qed
  
lemma lim_B: "(\<lambda>n. measure source (B n)) \<longlonglongrightarrow> 0"
proof -        
  have measure_B_le: "measure source (B n) \<le> (\<Sum>m. measure source (A (m + n)))" for n
    apply (rule proc_source.finite_measure_subadditive_countably)
     apply auto[1]
    apply (subst summable_iff_shift)
    using summable_A by blast
  have lim_A: "(\<lambda>n. (\<Sum>m. measure source (A (m + n)))) \<longlonglongrightarrow> 0"
    by (fact suminf_exist_split2[OF summable_A])
  have "convergent (\<lambda>n. measure source (B n))"
    apply (intro Bseq_monoseq_convergent BseqI'[where K="measure source (\<Union> (range A))"])
    apply simp
     apply (meson A_measurable UNIV_I Union_mono image_iff image_subsetI proc_source.finite_measure_mono sets.countable_UN)
    apply (rule decseq_imp_monoseq)
    unfolding decseq_def
    using Union_add_subset proc_source.finite_measure_mono
    by (metis A_measurable countable_Un_Int(1))
  then obtain L where lim_B: "(\<lambda>n. measure source (B n)) \<longlonglongrightarrow> L"
    unfolding convergent_def by auto
  then have "L \<ge> 0"
    by (simp add: LIMSEQ_le_const)
  moreover have "L \<le> 0"
    using measure_B_le by (simp add: LIMSEQ_le[OF lim_B lim_A])
  ultimately show ?thesis
    using lim_B by simp
qed

lemma N_null: "N \<in> null_sets source"
proof -
  have "(\<lambda>n. measure source (B n)) \<longlonglongrightarrow> measure source N"
    apply (rule proc_source.finite_Lim_measure_decseq)
      using A_measurable apply blast
      apply (intro monotoneI, simp add: Union_add_subset)
    done
  then have "measure source N = 0"
    using lim_B LIMSEQ_unique by blast
  then show ?thesis
    by (auto simp add: emeasure_eq_ennreal_measure)
qed

lemma notin_N_index:
  assumes "\<omega> \<in> space source - N"
  obtains n\<^sub>0 where "\<omega> \<notin> (\<Union>n. A (n + n\<^sub>0))"
  using assms by blast

context
  fixes \<omega>
  assumes \<omega>: "\<omega> \<in> space source - N"
begin

(* EXPERIMENTAL addition of n\<^sub>0 > 0 - removes an edge case *)
definition "n\<^sub>0 \<equiv> SOME m. \<omega> \<notin> (\<Union>n. A (n + m)) \<and> m > 0"

lemma
  shows n_zero: "\<omega> \<notin> (\<Union>n. A (n + n\<^sub>0))"
    and n_zero_nonzero: "n\<^sub>0 > 0"
proof -
  have "\<exists>m. \<omega> \<notin> (\<Union>n. A (n + m))"
    using \<omega> by blast
  then have "\<exists>m. \<omega> \<notin> (\<Union>n. A (n + m)) \<and> m > 0"
    by (metis (no_types, lifting) UNIV_I UN_iff add.comm_neutral not_gr_zero zero_less_Suc)
  then have "\<omega> \<notin> (\<Union>n. A (n + n\<^sub>0)) \<and> n\<^sub>0 > 0"
    unfolding n\<^sub>0_def by (rule someI_ex)
  then show "\<omega> \<notin> (\<Union>n. A (n + n\<^sub>0))" "n\<^sub>0 > 0"
    by blast+
  qed

lemma nzero_ge: "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> 2^n * T \<ge> 1"
proof (rule ccontr)
  fix n assume "n\<^sub>0 \<le> n" "\<not> 1 \<le> 2 ^ n * T"
  then have "A n = space source"
    unfolding A_def by simp
  then have "space source \<subseteq> (\<Union>m. A (m + n))"
    by (smt (verit, del_insts) UNIV_I UN_upper add_0)
  also have "(\<Union>m. A (m + n)) \<subseteq> (\<Union>m. A (m + n\<^sub>0))"
    by (simp add: Union_add_subset \<open>n\<^sub>0 \<le> n\<close>)
  finally show False
    using \<omega> n_zero by blast
qed

lemma omega_notin: "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> \<omega> \<notin> A n"
    by (metis n_zero UNIV_I UN_iff add.commute le_Suc_ex)

lemma X_dyadic_incr:
  assumes "k \<in> {1..\<lfloor>2^n * T\<rfloor>}" "n \<ge> n\<^sub>0"
  shows "dist (X ((real_of_int k-1)/2^n) \<omega>) (X (real_of_int k/2^n) \<omega>) < 2 powr (- \<gamma> * n)"
proof -
  have "finite {1..\<lfloor>2^n * T\<rfloor>}" "{1..\<lfloor>2^n * T\<rfloor>} \<noteq> {}"
    using assms nzero_ge by blast+
  then have fin_nonempty: "finite {dist (X (real_of_int (k - 1) * 2 powr - real n) \<omega>) (X (real_of_int k * 2 powr - real n) \<omega>) |k.
             k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}}" "{dist (X (real_of_int (k - 1) * 2 powr - real n) \<omega>) (X (real_of_int k * 2 powr - real n) \<omega>) |k.
             k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}} \<noteq> {}"
    by fastforce+
  have "2 powr (- \<gamma> * real n)
     > Max {dist (X (real_of_int (k - 1) * 2 powr - real n) \<omega>) (X (real_of_int k * 2 powr - real n) \<omega>) |k.
             k \<in> {1..\<lfloor>2 ^ n * T\<rfloor>}}"
    using nzero_ge[OF assms(2)] omega_notin[OF assms(2)] \<omega> A_def by auto
  then have "2 powr (- \<gamma> * real n) > dist (X (real_of_int (k - 1) * 2 powr - real n) \<omega>) (X (real_of_int k * 2 powr - real n) \<omega>)"
    using Max_less_iff[OF fin_nonempty] assms(1) by blast
  then show ?thesis
    by (simp, smt (verit, ccfv_threshold) divide_powr_uminus powr_realpow)
qed

lemma dist_dyadic_fixed:
  assumes mn: "m \<ge> n" "n \<ge> n\<^sub>0"
  and s_dyadic: "s \<in> dyadic_interval_step m 0 T"
  and t_dyadic: "t \<in> dyadic_interval_step m 0 T"
  and st: "s \<le> t" "t - s \<le> 1/2^n"
shows "dist (X t \<omega>) (X s \<omega>) \<le> 2 * 2 powr (- \<gamma> * n) / (1 - 2 powr - \<gamma>)"
proof -
  define u where "u \<equiv> \<lfloor>2^n * s\<rfloor> / 2^n"
  have "u = Max (dyadic_interval_step n 0 s)"
    unfolding u_def
    apply (rule dyadic_interval_step_Max[symmetric])
    apply (rule dyadics_geq[OF s_dyadic])
    done
  then have "u \<in> dyadic_interval_step n 0 T"
    using dyadic_interval_step_mem dyadics_geq dyadics_leq s_dyadic u_def by force
  then have u_dyadic: "u \<in> dyadic_interval_step m 0 T"
    using mn(1) dyadic_interval_step_subset by blast
  have "u \<le> s"
    unfolding u_def using floor_pow2_leq by blast
  have "s < u + 1/2^n"
    unfolding u_def apply (simp add: field_simps)
    using floor_le_iff apply linarith
    done
  have "u \<le> t"
    using \<open>u \<le> s\<close> st(1) by linarith
  have "t < u + 2/2^n"
    using \<open>s <u + 1/2^n\<close> st(2) by force
  then have "t - u < 2/2^n"
    by linarith
  then have "t - u < 1"
    by (smt (verit) mn(2) n_zero_nonzero One_nat_def Suc_leI divide_le_eq_1_pos
        power_increasing power_one_right)
  obtain b_tu k_tu where tu_exp: "dyadic_expansion (t-u) m T b_tu k_tu"
    using dyadic_expansion_ex dyadic_interval_minus[OF u_dyadic t_dyadic \<open>u \<le> t\<close>] by blast
  then have "k_tu = 0"
    using dyadic_expansion_floor[OF tu_exp] \<open>t - u < 1\<close> \<open>u \<le> t\<close> by linarith
  show ?thesis
    using X_dyadic_incr sorry
qed

definition "C\<^sub>0 \<equiv> 2 powr (1 + \<gamma>) / (1 - 2 powr - \<gamma>)"

lemma C_zero_ge[simp]: "C\<^sub>0 > 0"
  unfolding C\<^sub>0_def using gt_0
  by (metis diff_gt_0_iff_gt divide_less_eq_1_pos gamma gr_one_powr greaterThanLessThan_iff 
      one_less_numeral_iff powr_gt_zero powr_minus_divide semiring_norm(76) zero_less_divide_iff 
      zero_neq_numeral)

lemma dist_dyadic:
  assumes  s: "s \<in> dyadic_interval 0 T"
      and t: "t \<in> dyadic_interval 0 T"
      and st_dist: "dist t s \<le> 1 / 2 ^ n\<^sub>0"
      and neq: "s \<noteq> t"
    shows  "dist (X t \<omega>) (X s \<omega>) \<le> C\<^sub>0 * (dist t s) powr \<gamma>"
proof -
  have "dist t s > 0"
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
  then show "dist (X t \<omega>) (X s \<omega>) \<le> C\<^sub>0 * (dist t s) powr \<gamma>"
    using dist_dyadic_fixed sorry
qed
    
definition "K \<equiv> \<lambda>t s. C\<^sub>0 * 2 powr ((1-\<gamma>) * n\<^sub>0) * (dist t s) powr \<gamma>"

lemma X_incr:
  assumes  "s \<in> dyadic_interval 0 T" and "t \<in> (dyadic_interval 0 T)"
  shows "dist (X t \<omega>) (X s \<omega>) \<le> K t s"
  using dist_dyadic sorry

lemma holder_dyadic: "\<gamma>-holder_on (dyadic_interval 0 T) (\<lambda>t. X t \<omega>)"
  apply (intro holder_onI)
  apply (fact gamma_0_1)
  apply (intro exI[where x="C\<^sub>0 * 2 powr ((1-\<gamma>) * n\<^sub>0)"])
  unfolding dyadic_interval_def C_zero_ge
  apply (auto simp: zero_less_divide_iff less_eq_real_def)
  by (metis K_def X_incr linorder_neqE_linordered_idom linorder_not_le mem_dyadic_interval)

lemma uniformly_continuous_dyadic: "uniformly_continuous_on (dyadic_interval 0 T) (\<lambda>t. X t \<omega>)"
  using holder_dyadic by (fact holder_uniform_continuous)

lemma Lim_exists: "\<exists>L. ((\<lambda>s. X s \<omega>) \<longlongrightarrow> L) (at t within (dyadic_interval 0 T))"
  if "t \<in> {0..T}"
  apply (rule uniformly_continuous_on_extension_at_closure[where x = t])
  using that dyadic_interval_dense uniformly_continuous_dyadic apply fast
  using that apply (simp add: dyadic_interval_dense)
  by blast

definition "L \<equiv> (\<lambda>t. (Lim (at t within dyadic_interval 0 T) (\<lambda>s. X s \<omega>)))"

definition X_tilde :: "real \<Rightarrow> 'b" where
        "X_tilde \<equiv> \<lambda>t. if t \<in> dyadic_interval 0 T then X t \<omega> else L t"

lemma dist_X_tilde: "dist (X_tilde s) (X_tilde t) \<le> K s t" if "s \<in> {0..T}" "t \<in> {0..T}" for s t
    sorry text \<open> Should be analogous to the proof of @{thm dist_dyadic} \<close>

lemma holder_X_tilde: "\<gamma>-holder_on {0..T} X_tilde"
      apply (intro holder_onI)
      using gamma_0_1 apply argo
      apply (intro exI[where x="C\<^sub>0 * 2 powr ((1-\<gamma>) * n\<^sub>0)"])
      using C_zero_ge apply (auto simp: zero_less_divide_iff)
       apply (simp add: less_eq_real_def)
      by (metis K_def atLeastAtMost_iff dist_X_tilde)

lemma local_holder_X_tilde: "local_holder_on \<gamma> {0..T} X_tilde"
      using holder_X_tilde holder_implies_local_holder by blast
end

definition default :: 'b where "default = (SOME x. True)"

definition X_tilde' :: "real \<Rightarrow> 'a \<Rightarrow> 'b" where
    "X_tilde' \<equiv> (\<lambda>t \<omega>. if \<omega> \<in> N then default else
                      (if t \<in> dyadic_interval 0 T then X t \<omega>
               else Lim (at t within dyadic_interval 0 T) (\<lambda>s. X s \<omega>)))"

lemma local_holder_X_tilde': "local_holder_on \<gamma> {0..T} (\<lambda>t. X_tilde' t \<omega>)"
    if "\<omega> \<in> space source" for \<omega>
proof (cases "\<omega> \<in> N")
  case True
  then show ?thesis
    unfolding X_tilde'_def using local_holder_const by fastforce
next
  case False
  then have 1: "\<omega> \<in> space source - N"
    using that by blast
  show ?thesis
    using local_holder_X_tilde[OF 1] L_def[OF 1]
    unfolding X_tilde_def[OF 1] X_tilde'_def
    by (simp only: False if_False)
qed

lemma X_eq_X_tilde_AE: "AE \<omega> in source. X t \<omega> = X_tilde' t \<omega>" if "t \<in> {0..T}" for t
proof (cases "t \<in> dyadic_interval 0 T")
  case True
  then have "\<omega> \<notin> N \<Longrightarrow> X t \<omega> = X_tilde' t \<omega>" for \<omega>
    unfolding X_tilde'_def by (simp only: if_True if_False)
  then have "{\<omega>. X t \<omega> \<noteq> X_tilde' t \<omega>} \<subseteq> N"
    by blast
  then show ?thesis
    apply (intro AE_I[where N="N"])
    using N_null by auto
next
  case False
  have "AE \<omega> in source. X t \<omega> = Lim (at t within dyadic_interval 0 T) (\<lambda>s. X s \<omega>)"
  proof -
    have "tendsto_measure source X (\<lambda>\<omega>. Lim (at t within dyadic_interval 0 T) (\<lambda>s. X s \<omega>)) (at t within dyadic_interval 0 T)"
      apply (intro measure_conv_imp_AE_at_within)
      unfolding Topological_Spaces.Lim_def apply (rule theI')
      using Lim_exists
      sorry
    then show ?thesis
      sorry
  qed
  moreover have "X_tilde' t \<omega> = Lim (at t within dyadic_interval 0 T) (\<lambda>s. X s \<omega>)" 
      if "\<omega> \<in> space source - N" for \<omega>
    unfolding X_tilde'_def using False that by auto
  then have "AE \<omega> in source. X_tilde' t \<omega> = Lim (at t within dyadic_interval 0 T) (\<lambda>s. X s \<omega>)"
    apply (simp add: eventually_ae_filter)
    apply (intro bexI[where x=N])
    using False X_tilde'_def apply auto[1]
    using N_null by blast
  ultimately show ?thesis
    by force
qed

lemma X_tilde_measurable[measurable]: "X_tilde' t \<in> borel_measurable source" if "t \<in> {0..T}" for t
  unfolding X_tilde'_def by measurable

lemma X_tilde_modification: "modification (restrict_index X {0..T})
   (prob_space.process_of source (proc_target X) {0..T} X_tilde' default)"
  apply (intro modificationI compatibleI)
     apply simp_all
  apply (subst restrict_index_source)
  using X_eq_X_tilde_AE by blast
end

context Kolmogorov_Chentsov
begin

lemma Kolmogorov_Chentsov_finite: "T > 0 \<Longrightarrow> Kolmogorov_Chentsov_finite X a b C \<gamma> T"
  by (simp add: Kolmogorov_Chentsov_axioms Kolmogorov_Chentsov_finite.intro Kolmogorov_Chentsov_finite_axioms_def)

definition "Mod \<equiv> \<lambda>T. SOME Y. modification (restrict_index X {0..T}) Y \<and> 
    (\<forall>x\<in>space source. local_holder_on \<gamma> {0..T} (\<lambda>t. Y t x))"

lemma Mod: "modification (restrict_index X {0..T}) (Mod T)"
  "(\<forall>x\<in>space source. local_holder_on \<gamma> {0..T} (\<lambda>t. (Mod T) t x)) " if "0 < T" for T
proof -
  interpret Kolmogorov_Chentsov_finite X a b C \<gamma> T
    using that by (simp add: Kolmogorov_Chentsov_finite)
  have "modification (restrict_index X {0..T}) (Mod T) \<and> 
    (\<forall>x\<in>space source. local_holder_on \<gamma> {0..T} (\<lambda>t. (Mod T) t x))"
    unfolding Mod_def apply (rule someI_ex)
    apply (rule exI[where x="prob_space.process_of source (proc_target X) {0..T} X_tilde' default"])    
    apply safe
     apply (fact  X_tilde_modification)
    using local_holder_X_tilde' apply auto
    by (smt (verit, del_insts) atLeastAtMost_iff local_holder_on_cong)
  then show "modification (restrict_index X {0..T}) (Mod T)"
            "(\<forall>x\<in>space source. local_holder_on \<gamma> {0..T} (\<lambda>t. (Mod T) t x)) " 
    by blast+
qed

lemma compatible_Mod: "compatible (restrict_index X {0..T}) (Mod T)" if "0 < T" for T
  using Mod that modificationD(1) by blast

lemma Mod_source[simp]: "proc_source (Mod T) = source"  if "0 < T" for T
  by (metis compatible_Mod compatible_source restrict_index_source that)

lemma Mod_target: "sets (proc_target (Mod T)) = sets (proc_target X)"  if "0 < T" for T
  by (metis compatible_Mod[OF that] compatible_target restrict_index_target)
  
lemma indistinguishable_mod:
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
    have "\<forall>x \<in> space source. continuous_on {0..S} (\<lambda>t. (Mod S) t x)"
      using Mod[OF that(1)] local_holder_imp_continuous by blast
    then have "\<forall>x \<in> space source. continuous_on {0..min S T} (\<lambda>t. (Mod S) t x)"
      using continuous_on_subset by fastforce
    then show ?case
      by (auto simp: that(1))
  next
    case (continuous_T)
    have "\<forall>x \<in> space source. continuous_on {0..T} (\<lambda>t. (Mod T) t x)"
      using Mod[OF that(2)] local_holder_imp_continuous by fast
    then have 2: "\<forall>x \<in> space source. continuous_on {0..min S T} (\<lambda>t. (Mod T) t x)"
      using continuous_on_subset by fastforce
    then show ?case
      by (auto simp: that(2))
  qed
qed

definition "N S T \<equiv> SOME N. N \<in> null_sets source \<and> {\<omega> \<in> space source. \<exists>t \<in> {0..min S T}. (Mod S) t \<omega> \<noteq> (Mod T) t \<omega>} \<subseteq> N" 

lemma N:
  assumes "S > 0" "T > 0"
  shows "N S T \<in> null_sets source \<and> {\<omega> \<in> space source. \<exists>t \<in> {0..min S T}. (Mod S) t \<omega> \<noteq> (Mod T) t \<omega>} \<subseteq> N S T"
proof -
  have ex: "\<forall>S > 0. \<forall>T > 0. \<exists>N. N \<in> null_sets source \<and> {\<omega> \<in> space source. \<exists>t \<in> {0..min S T}.
   (Mod S) t \<omega> \<noteq> (Mod T) t \<omega>} \<subseteq> N"
    apply (fold Bex_def)
    using indistinguishable_mod[THEN indistinguishable_null_ex] by simp
  show ?thesis
    unfolding N_def apply (rule someI_ex)
    using ex assms by blast
qed

definition N_inf where "N_inf \<equiv> (\<Union>S \<in> \<nat> - {0}. (\<Union> T \<in> \<nat> - {0}. N S T))"

lemma N_inf_null: "N_inf \<in> null_sets source"
  unfolding N_inf_def
  apply (intro null_sets_UN')
   apply (rule countable_Diff)
    apply (simp add: Nats_def)+
  using N by force

lemma Mod_eq_N_inf: "(Mod S) t \<omega> = (Mod T) t \<omega>"
    if "\<omega> \<in> space source - N_inf" "t \<in> {0..min S T}" "S \<in> \<nat> - {0}" "T \<in> \<nat> - {0}" for \<omega> t S T
proof -
  have "\<omega> \<in> space source - N S T"
    using that(1,3,4) unfolding N_inf_def by blast
  moreover have "S > 0" "T > 0"
    using that(2,3,4) by auto
  ultimately have "\<omega> \<in> {\<omega> \<in> space source. \<forall>t \<in>{0..min S T}. (Mod S) t \<omega> = (Mod T) t \<omega>}"
    using N by auto
  then show ?thesis
    using that(2) by blast
qed

definition default :: 'b where "default = (SOME x. True)"

definition "X_mod \<equiv> \<lambda>t \<omega>. if \<omega> \<in> space source - N_inf then (Mod \<lfloor>t+1\<rfloor>) t \<omega> else default"

definition "X_mod_process \<equiv> prob_space.process_of source (proc_target X) {0..} X_mod default" 

lemma Mod_measurable[measurable]: "\<forall>t\<in>{0..}. X_mod t \<in> source \<rightarrow>\<^sub>M proc_target X"
proof (intro ballI)
  fix t :: real assume "t \<in> {0..}"
  then have "0 < \<lfloor>t + 1\<rfloor>"
    by force
  then show "X_mod t \<in> source \<rightarrow>\<^sub>M proc_target X"
    unfolding X_mod_def apply measurable
      apply (subst measurable_cong_sets[where M'= "proc_source (Mod \<lfloor>t + 1\<rfloor>)" and N' = "proc_target (Mod \<lfloor>t + 1\<rfloor>)"])
    using Mod_source \<open>0 < \<lfloor>t + 1\<rfloor>\<close> apply presburger
    using Mod_target \<open>0 < \<lfloor>t + 1\<rfloor>\<close> apply presburger
      apply (meson random_process)
    apply simp
    apply (metis N_inf_null Int_def null_setsD2 sets.Int_space_eq1 sets.compl_sets)
    done
qed

lemma modification_X_mod_process: "modification X X_mod_process"
proof (intro modificationI ballI)
  show "compatible X X_mod_process"
    apply (intro compatibleI)
    unfolding X_mod_process_def
      apply (subst proc_source.source_process_of)
    using Mod_measurable proc_source.prob_space_axioms apply auto
    done
  fix t assume "t \<in> proc_index X"
  then have "t \<in> {0..}"
    by simp
  then have "real_of_int \<lfloor>t\<rfloor> + 1 > 0"
    by (simp add: add.commute add_pos_nonneg)
  then have "\<exists>N \<in> null_sets source. \<forall>\<omega> \<in> space source - N. 
      X t \<omega> = (prob_space.process_of source (proc_target X) {0..} X_mod default) t \<omega>"
  proof -
    have 1: "(prob_space.process_of source (proc_target X) {0..} X_mod default) t \<omega> = (Mod (real_of_int \<lfloor>t\<rfloor> + 1)) t \<omega>"
        if "\<omega> \<in> space source - N_inf" for \<omega>
      apply (subst proc_source.process_process_of)
      apply measurable
      unfolding X_mod_def using that \<open>t \<in> {0..}\<close> apply simp
      done
    have "\<exists>N \<in> null_sets source. \<forall>\<omega> \<in> space source - N. X t \<omega> = (Mod (real_of_int \<lfloor>t\<rfloor> + 1)) t \<omega>"
    proof -
      obtain N where "{x \<in> space source. (restrict_index X {0..real_of_int \<lfloor>t\<rfloor> + 1}) t x \<noteq> (Mod (real_of_int \<lfloor>t\<rfloor> + 1)) t x} \<subseteq> N \<and>
    N \<in> null_sets (proc_source (restrict_index X {0..(real_of_int \<lfloor>t\<rfloor> + 1)}))"
        using Mod(1)[OF \<open>real_of_int \<lfloor>t\<rfloor> + 1 > 0\<close>, THEN modification_null_set, of t]
        using \<open>t \<in> {0..}\<close> sorry
      then show ?thesis
        by (smt (verit, ccfv_threshold) DiffE mem_Collect_eq restrict_index_process restrict_index_source subset_eq)
    qed
    then obtain N where "N \<in> null_sets source" "\<forall>\<omega> \<in> space source - N. X t \<omega> = (Mod (real_of_int \<lfloor>t\<rfloor> + 1)) t \<omega>"
      by blast
    then show ?thesis
      apply (intro bexI[where x="N \<union> N_inf"])
       apply (metis 1 DiffE DiffI UnCI)
      using N_inf_null by blast
  qed
  then show "AE x in source. X t x = X_mod_process t x"
    by (smt (verit, del_insts) X_mod_process_def DiffI eventually_ae_filter mem_Collect_eq subsetI)
qed

lemma local_holder_X_mod: "local_holder_on \<gamma> {0..} (\<lambda>t. X_mod t \<omega>)" for \<omega>
proof (cases "\<omega> \<in> space source - N_inf")
  case False
  then show ?thesis
   apply (simp only: X_mod_def)
    apply (metis local_holder_const gamma_0_1)
    done
next
  case True
  then have \<omega>: "\<omega> \<in> space source" "\<omega> \<notin> N_inf"
    by simp_all
  then show ?thesis
  proof (intro local_holder_ballI[OF gamma_0_1] ballI)
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
        apply (rule gamma_0_1)
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
        using \<open>t \<in> {0..}\<close> apply safe
        apply (metis (no_types, opaque_lifting) floor_in_Nats Nats_1 Nats_add Nats_cases of_int_of_nat_eq of_nat_in_Nats)
          apply linarith
         apply (smt (verit) Int_iff Nats_1 Nats_add Nats_altdef1 atLeast_iff mem_Collect_eq s zero_le_floor)
        apply (metis Int_iff atLeast_iff floor_correct linorder_not_less one_add_floor s)
        done
      ultimately have "dist (X_mod r \<omega>) (X_mod s \<omega>) \<le> C * dist r s powr \<gamma>"
        using eC(3)[OF rs_ball] by simp
    }
    then show "\<exists>\<epsilon>>0. \<exists>C\<ge>0. \<forall>r\<in>ball t \<epsilon> \<inter> {0..}. \<forall>s\<in>ball t \<epsilon> \<inter> {0..}. dist (X_mod r \<omega>) (X_mod s \<omega>) \<le> C * dist r s powr \<gamma>"
      using e' eC(2) by blast
  qed
qed

lemma local_holder_X_mod_process: "local_holder_on \<gamma> {0..} (\<lambda>t. X_mod_process t \<omega>)" for \<omega>
  unfolding X_mod_process_def
  by (smt (verit, best) Mod_measurable UNIV_I local_holder_X_mod local_holder_on_cong
      proc_source.process_process_of space_borel target_borel)
end
end
