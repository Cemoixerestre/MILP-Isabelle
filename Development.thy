theory Development
  imports
    Linear_Inequalities.Mixed_Integer_Solutions (* mixed integer bounds *)
    Simplex.Simplex_Incremental (* incremental simplex algorithm *)
    Farkas.Matrix_Farkas (* existing connection between simplex and matrices, perhaps needs generalization *)
    Simplex.Abstract_Linear_Poly
begin

(* to be started with

isabelle jedit -d /path/to/afp-2019/thys -l Linear_Inequalities Development.thy

for Isabelle 2019 and corresponding AFP (afp-2019-06-21 from https://www.isa-afp.org or later)

*)

(* reenable Var without prefix *)
abbreviation Var where "Var \<equiv> Abstract_Linear_Poly.Var"
abbreviation max_var where "max_var \<equiv> Abstract_Linear_Poly.max_var"
abbreviation vars_list where "vars_list \<equiv> Abstract_Linear_Poly.vars_list"

fun satisfies_mixed_constraints (infixl "\<Turnstile>\<^sub>m\<^sub>c\<^sub>s" 100) where
"v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (cs, I) = (v \<Turnstile>\<^sub>c\<^sub>s cs \<and> (\<forall> i \<in> I. v i \<in> \<int>))"

(* For the moment, the type of branch_and_bound is sufficient to solve
  mixed-integer linear problems, but it should be updated afterwards by:
  - Taking into account indices
  - Returning an unsat core when the problem is infeasible instead of just
    returning `None`
Also, maybe the argument types could be changed to be more efficient, but it
is not the priority now.
*)

text \<open>We define the following measure on the arguments of the branch-and-bound
algorithm to prove its termination.
The idea is that at each recursive call ("branch operation"), if the branch
is performed on the variable x, then the quantity ub x - lb x strictly
decreases while the other ones are left unchanged.
Finally, if the sum of the ub x - lb x is nonpositive, then the problem
has an unique solution with integral values for the elements of Is, or is
infeasible.\<close>
fun bb_measure where
"bb_measure (_, Is, lb, ub) = nat (sum_list (map (\<lambda> x. ub x - lb x) Is))"

definition bounds_to_constraints where
  "bounds_to_constraints Is lb ub =
     map (\<lambda> x. GEQ (Var x) (of_int (lb x))) Is @
     map (\<lambda> x. LEQ (Var x) (of_int (ub x))) Is"

lemma bounds_to_constraints_sat:
  "v \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is lb ub) \<longleftrightarrow>
   (\<forall> i \<in> set Is. of_int (lb i) \<le> v i \<and> v i \<le> of_int (ub i))"
proof -
  {
    fix i
    assume v: "v \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is lb ub)"
    assume "i \<in> set Is"
    hence "GEQ (Var i) (of_int (lb i)) \<in> set (bounds_to_constraints Is lb ub)"
      and "LEQ (Var i) (of_int (ub i)) \<in> set (bounds_to_constraints Is lb ub)"
      unfolding bounds_to_constraints_def by auto
    hence "v \<Turnstile>\<^sub>c GEQ (Var i) (of_int (lb i)) \<and>
           v \<Turnstile>\<^sub>c LEQ (Var i) (of_int (ub i))" using v by blast
    hence  "of_int (lb i) \<le> v i \<and> v i \<le> of_int (ub i)"
      using valuate_Var[of i v] by auto
  }
  moreover
  {
    fix c
    assume bnd: "(\<forall> i \<in> set Is. of_int (lb i) \<le> v i \<and> v i \<le> of_int (ub i))"
    assume "c \<in> set (bounds_to_constraints Is lb ub)"
    then obtain i where i: "i \<in> set Is" 
                  and "c = GEQ (Var i) (of_int (lb i)) \<or>
                       c = LEQ (Var i) (of_int (ub i))"
      unfolding bounds_to_constraints_def by auto
    hence "v \<Turnstile>\<^sub>c c" using i bnd valuate_Var[of i v] by fastforce
  }
  ultimately show ?thesis by blast
qed

lemma sat_impl_sum_diff_bounds_nonneg:
  assumes sat: "simplex (cs @ bounds_to_constraints Is lb ub) = Sat v"
  and J: "set J \<subseteq> set Is"
  shows "(\<Sum>x\<leftarrow>J. ub x - lb x) \<ge> 0"
proof (rule sum_list_nonneg)
  fix y assume "y \<in> set (map (\<lambda>x. ub x - lb x) J)"
  then obtain x where x: "x \<in> set J" and y: "y = ub x - lb x" by auto
  from sat have "\<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is lb ub)"
    using simplex(3) by fastforce
  hence "\<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints J lb ub)"
    unfolding bounds_to_constraints_def using J by auto
  hence "of_int (lb x) \<le> \<langle>v\<rangle> x \<and> \<langle>v\<rangle> x \<le> of_int (ub x)"
    using bounds_to_constraints_sat x by blast
  hence "ub x - lb x \<ge> 0" by linarith
  thus "y \<ge> 0" using y by blast
qed

lemma find_Some_set:
  assumes "find P xs = Some x"
  shows "x \<in> set xs \<and> P x"
proof -
  from assms obtain i where "x = xs ! i" and "i < length xs" and "P (xs ! i)"
    using find_Some_iff[of P xs x] by blast
  thus ?thesis by auto
qed

lemma nonnint_sat_pos_measure:
  assumes sat: "simplex (cs @ bounds_to_constraints Is lb ub) = Sat v"
  assumes find: "find (\<lambda>y. \<langle>v\<rangle> y \<notin> \<int>) Is = Some x"
  shows "0 < (\<Sum>x\<leftarrow>Is. ub x - lb x)"
proof -
  have x: "x \<in> set Is" and "\<langle>v\<rangle> x \<notin> \<int>" using find_Some_set[OF find] by auto
  from sat simplex(3) have "\<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is lb ub)"
    by auto
  hence "of_int (lb x) \<le> \<langle>v\<rangle> x \<and> \<langle>v\<rangle> x \<le> of_int (ub x)"
    using bounds_to_constraints_sat x by blast
  (* I wonder why the automatic provers perform badly with `rat_of_int`.
     I have to add an intermediary step, and I also have to tell
     explicitely `metis` to use `Ints_of_int`. Even if I add explicitely this
     lemma, metis is the only prover that manages to use it. *)
  hence "rat_of_int (lb x) \<ge> rat_of_int (ub x) \<Longrightarrow> rat_of_int (lb x) = \<langle>v\<rangle> x"
    by linarith
  hence "\<not> (rat_of_int (lb x) \<ge> rat_of_int (ub x))"
    using `\<langle>v\<rangle> x \<notin> \<int>` Ints_of_int by metis

  hence "0 < ub x - lb x" by linarith
  moreover have "0 \<le> (\<Sum>i\<leftarrow>remove1 x Is. ub i - lb i)"
    using set_remove1_subset
    by (rule sat_impl_sum_diff_bounds_nonneg[OF sat])
  ultimately have "0 < (ub x - lb x) + (\<Sum>i\<leftarrow>remove1 x Is. ub i - lb i)"
    by linarith
  also have "\<dots> = (\<Sum>i\<leftarrow>Is. ub i - lb i)"
    using sum_list_map_remove1[OF x, of "\<lambda> i. ub i - lb i"] by auto
  finally show ?thesis by blast
qed

text \<open>The core of a branch-and-bound solver for mixed-integer linear problems.
It takes as arguments a constraint list, the list of integral variables, and
functions mapping integral variables to lower and upper-bounds\<close>
function branch_and_bound_core ::
  "constraint list \<Rightarrow> var list \<Rightarrow> (var \<Rightarrow> int) \<Rightarrow> (var \<Rightarrow> int)
     \<Rightarrow> rat valuation option" where
  "branch_and_bound_core cs Is lb ub =
    (case simplex (cs @ bounds_to_constraints Is lb ub) of
       Unsat _ \<Rightarrow> None
     | Sat r \<Rightarrow> (let v = \<langle>r\<rangle> in
         case find (\<lambda> x. v x \<notin> \<int>) Is of
           None \<Rightarrow> Some v
         | Some x \<Rightarrow> (let lb' = (\<lambda> y. if y = x then \<lceil>v x\<rceil> else lb y) in
            let ub' = (\<lambda> y. if y = x then \<lfloor>v x\<rfloor> else ub y) in
            let sol = branch_and_bound_core cs Is lb ub' in
            if sol \<noteq> None then sol else branch_and_bound_core cs Is lb' ub)))"
  by pat_completeness auto
termination
proof (relation "measure bb_measure", force, goal_cases)
  case (1 cs Is lb ub v vv x lb' ub')
  hence sat: "simplex (cs @ bounds_to_constraints Is lb ub) = Sat v"
   and x: "find (\<lambda>i. \<langle>v\<rangle> i \<notin> \<int>) Is = Some x" by auto
  let ?ub' = "\<lambda> i. (if i = x then  \<lfloor>\<langle>v\<rangle> x\<rfloor> else ub i)" 
  from find_Some_set[OF x] have x: "x \<in> set Is" and "\<langle>v\<rangle> x \<notin> \<int>" by auto

  from sat simplex(3) have "\<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is lb ub)"
    by auto
  hence "\<langle>v\<rangle> x \<le> of_int (ub x)" using bounds_to_constraints_sat x by blast
  hence ub'x: "\<lfloor>\<langle>v\<rangle> x\<rfloor> < ub x" using floor_less[OF \<open>\<langle>v\<rangle> x \<notin> \<int>\<close>] by linarith

  have "(\<Sum>i\<leftarrow>Is. ?ub' i - lb i) = ?ub' x - lb x +
                                   (\<Sum>i\<leftarrow>remove1 x Is. ?ub' i - lb i)"
    using sum_list_map_remove1[OF x] by blast
  moreover have "?ub' x - lb x < ub x - lb x" using ub'x by auto
  moreover have "(\<Sum>i\<leftarrow>remove1 x Is. ?ub' i - lb i) \<le>
                 (\<Sum>i\<leftarrow>remove1 x Is. ub i - lb i)"
    by(rule sum_list_mono, insert ub'x, simp)
  moreover have "(\<Sum>i\<leftarrow>Is. ub i - lb i) =
                 ub x - lb x + (\<Sum>i\<leftarrow>remove1 x Is. ub i - lb i)"
    using sum_list_map_remove1[OF x] by blast
  ultimately have "(\<Sum>i\<leftarrow>Is. ?ub' i - lb i) < (\<Sum>i\<leftarrow>Is. ub i - lb i)"
    by linarith 
  thus ?case using nonnint_sat_pos_measure 1 by auto
next
  case (2 cs Is lb ub v vv x lb' ub' sol)
  hence sat: "simplex (cs @ bounds_to_constraints Is lb ub) = Sat v"
    and x: "find (\<lambda>i. \<langle>v\<rangle> i \<notin> \<int>) Is = Some x" by auto
  let ?lb' = "\<lambda> i. if i = x then \<lceil>\<langle>v\<rangle> x\<rceil> else lb i"
  from find_Some_set[OF x] have x: "x \<in> set Is" and "\<langle>v\<rangle> x \<notin> \<int>" by auto

  from sat simplex(3) have "\<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is lb ub)"
    by auto
  hence "of_int (lb x) \<le> \<langle>v\<rangle> x" using bounds_to_constraints_sat x by blast
  hence lb'x: "lb x < \<lceil>\<langle>v\<rangle> x\<rceil>" using less_ceiling_iff[of "lb x" "\<langle>v\<rangle> x"]
    by (metis Ints_of_int \<open>\<langle>v\<rangle> x \<notin> \<int>\<close> order.not_eq_order_implies_strict)
  
  have "(\<Sum>i\<leftarrow>Is. ub i - ?lb' i) = ub x - ?lb' x +
                                   (\<Sum>i\<leftarrow>remove1 x Is. ub i - ?lb' i)"
    using sum_list_map_remove1[OF x] by blast
  moreover have "ub x - ?lb' x < ub x - lb x" using lb'x by auto
  moreover have "(\<Sum>i\<leftarrow>remove1 x Is. ub i - ?lb' i) \<le>
                 (\<Sum>i\<leftarrow>remove1 x Is. ub i - lb i)"
    by(rule sum_list_mono, insert lb'x, simp)
  moreover have "(\<Sum>i\<leftarrow>Is. ub i - lb i) =
                 ub x - lb x + (\<Sum>i\<leftarrow>remove1 x Is. ub i - lb i)"
    using sum_list_map_remove1[OF x] by blast
  ultimately have "(\<Sum>i\<leftarrow>Is. ub i - ?lb' i) < (\<Sum>i\<leftarrow>Is. ub i - lb i)"
    by linarith
  thus ?case using nonnint_sat_pos_measure 2 by auto
qed

(* as they make the simplifier non-terminate *)
declare branch_and_bound_core.simps[simp del]

lemma branch_and_bound_core_sat:
  "branch_and_bound_core cs Is lb ub = Some v \<Longrightarrow> v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, set Is)"
proof (induction rule: branch_and_bound_core.induct)
  case (1 cs Is lb ub)
  note [simp] = branch_and_bound_core.simps[of cs Is lb ub] (* activate simp-rules only for lb ub *)
  show ?case

  proof (cases "simplex (cs @ bounds_to_constraints Is lb ub)")
    case (Inr r)
    hence r: "\<langle>r\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (cs @ bounds_to_constraints Is lb ub)"
      using simplex(3) by blast
    show ?thesis

    proof (cases "find (\<lambda> x. \<langle>r\<rangle> x \<notin> \<int>) Is")
      case None
      hence "\<forall> i \<in> set Is. \<langle>r\<rangle> i \<in> \<int>"
        using find_None_iff[of _ Is] by simp
      hence r: "\<langle>r\<rangle> \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, set Is)" using r by auto
      have "branch_and_bound_core cs Is lb ub = Some \<langle>r\<rangle>"
        by (simp add: Inr None)
      hence "\<langle>r\<rangle> = v" using Inr 1(3) by auto
      thus ?thesis using r by blast

    next

      case (Some x)
      define lb' where "lb' = (\<lambda> y. if y = x then \<lceil>\<langle>r\<rangle> x\<rceil> else lb y)"
      define ub' where "ub' = (\<lambda> y. if y = x then \<lfloor>\<langle>r\<rangle> x\<rfloor> else ub y)"
      define sol where "sol = branch_and_bound_core cs Is lb ub'"
      show ?thesis
      proof (cases)
        assume sol: "sol = None"
        hence "branch_and_bound_core cs Is lb ub =
               branch_and_bound_core cs Is lb' ub"
          using Inr Some lb'_def ub'_def sol_def by simp
        hence "branch_and_bound_core cs Is lb' ub = Some v"
          using 1(3) by presburger
        thus ?thesis using sol 1(2)[OF Inr _ Some lb'_def ub'_def sol_def]
          by fast
      
      next
      
        assume sol: "sol \<noteq> None"
        hence "branch_and_bound_core cs Is lb ub = sol"
          using Inr Some unfolding sol_def ub'_def by force
        hence "sol = Some v" using 1(3) by blast
        thus ?thesis
          using 1(1)[OF Inr _ Some lb'_def ub'_def]
          unfolding sol_def by blast
      qed
    qed
  qed (insert 1, auto)
qed

lemma int_le_floor_iff:
  assumes "x \<in> \<int>"
  shows "x \<le> y \<longleftrightarrow> x \<le> of_int \<lfloor>y\<rfloor>"
proof
  assume "x \<le> y"
  thus "x \<le> of_int \<lfloor>y\<rfloor>"
    using le_floor_iff[of "\<lfloor>x\<rfloor>" "y"] floor_of_int_eq[OF assms] by auto
next
  assume "x \<le> of_int \<lfloor>y\<rfloor>"
  thus "x \<le> y"
    using le_floor_iff[of "\<lfloor>x\<rfloor>" "of_int \<lfloor>y\<rfloor>"] floor_of_int_eq[OF assms]
    by linarith
qed

lemma int_ge_ceiling_iff:
  assumes "x \<in> \<int>"
  shows "x \<ge> y \<longleftrightarrow> x \<ge> of_int \<lceil>y\<rceil>"
  unfolding ceiling_def
  using int_le_floor_iff[of "-x" "-y"] assms by fastforce

lemma branch_and_bound_core_unsat:
  "branch_and_bound_core c Is lb ub = None \<Longrightarrow>
   \<forall> i \<in> set Is. of_int (lb i) \<le> v i \<and> v i \<le> of_int (ub i) \<Longrightarrow>
   \<not> (v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set c, set Is))"
proof (induction rule: branch_and_bound_core.induct)
  case (1 cs Is lb ub)
  note [simp] = branch_and_bound_core.simps[of cs Is lb ub] (* activate simp-rules only for lb ub *)
  show ?case
  proof (cases "simplex (cs @ bounds_to_constraints Is lb ub)")
    case Inl
    from bounds_to_constraints_sat[of Is lb ub v] 1(4)
    have "v \<Turnstile>\<^sub>c\<^sub>s set (bounds_to_constraints Is lb ub)" by blast
    hence "\<not> (v \<Turnstile>\<^sub>c\<^sub>s set cs)" using simplex(1)[OF Inl] by auto
    thus ?thesis by auto
  next
    case (Inr r)
    hence r: "\<langle>r\<rangle> \<Turnstile>\<^sub>c\<^sub>s set (cs @ bounds_to_constraints Is lb ub)"
      using simplex(3) by blast
    show ?thesis
    proof (cases "find (\<lambda> x. \<langle>r\<rangle> x \<notin> \<int>) Is")
      case None
      have "branch_and_bound_core cs Is lb ub = Some \<langle>r\<rangle>"
        by (simp add: Inr None)
      thus ?thesis using 1(3) by auto
    next

      case (Some x)
      hence x: "x \<in> set Is" and rx: "\<langle>r\<rangle> x \<notin> \<int>"
        using find_Some_set[of _ Is x] by (blast, blast)
      define lb' where "lb' = (\<lambda> y. if y = x then \<lceil>\<langle>r\<rangle> x\<rceil> else lb y)"
      define ub' where "ub' = (\<lambda> y. if y = x then \<lfloor>\<langle>r\<rangle> x\<rfloor> else ub y)"
      define sol where "sol = branch_and_bound_core cs Is lb ub'"
      show ?thesis
      proof (cases, standard)

        assume v: "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, set Is)"
        assume sol: "sol = None"
        from v have "v x \<in> \<int>" using x by simp
        show False
        proof cases

          assume "v x \<le> \<langle>r\<rangle> x"
          hence "v x \<le> of_int \<lfloor>\<langle>r\<rangle> x\<rfloor>"
            using int_le_floor_iff[OF \<open>v x \<in> \<int>\<close>] by blast
          hence "\<forall>i\<in>set Is. of_int (lb i) \<le> v i \<and> v i \<le> of_int (ub' i)"
            using 1(4) unfolding ub'_def by auto
          thus False
            using 1(1)[OF Inr _ Some lb'_def ub'_def sol[unfolded sol_def]] v
            by blast

        next

          assume "~ (v x \<le> \<langle>r\<rangle> x)"
          hence "v x \<ge> \<langle>r\<rangle> x" by linarith
          hence "v x \<ge> of_int \<lceil>\<langle>r\<rangle> x\<rceil>"
            using int_ge_ceiling_iff[OF \<open>v x \<in> \<int>\<close>] by blast
          hence bnds: "\<forall>i\<in>set Is. of_int (lb' i) \<le> v i \<and> v i \<le> of_int (ub i)"
            using 1(4) unfolding lb'_def by auto

          from sol have "branch_and_bound_core cs Is lb ub =
                         branch_and_bound_core cs Is lb' ub"
            using Inr Some lb'_def ub'_def sol_def by simp
          hence sol_lb': "branch_and_bound_core cs Is lb' ub = None"
            using 1(3) by argo
          thus False
            using 1(2)[OF Inr _ Some lb'_def ub'_def sol_def _ sol_lb' bnds]
                  sol v by blast
        qed

      next
        assume sol: "sol \<noteq> None"
        hence "branch_and_bound_core cs Is lb ub = sol"
          using Inr Some unfolding sol_def ub'_def by force
        thus ?thesis using 1(3) sol by fast
      qed
    qed
  qed
qed

abbreviation (input) "Ltc \<equiv> Le_Constraint Lt_Rel"

(* There already exists a function `lec_of_constraint`, but it does not handle every
   cases. *)
primrec constraint_to_le_constraint where
  "constraint_to_le_constraint (LEQ l x) = [Leqc l x]"
| "constraint_to_le_constraint (GEQ l x) = [Leqc (-l) (-x)]"
| "constraint_to_le_constraint (LT l x) = [Ltc l x]"
| "constraint_to_le_constraint (GT l x) = [Ltc (-l) (-x)]"
| "constraint_to_le_constraint (EQ l x) = [Leqc l x, Leqc (-l) (-x)]"
| "constraint_to_le_constraint (LEQPP l0 l1) = [Leqc (l0 - l1) 0]"
| "constraint_to_le_constraint (GEQPP l0 l1) = [Leqc (l1 - l0) 0]"
| "constraint_to_le_constraint (LTPP l0 l1) = [Ltc (l0 - l1) 0]"
| "constraint_to_le_constraint (GTPP l0 l1) = [Ltc (l1 - l0) 0]"
| "constraint_to_le_constraint (EQPP l0 l1) = [Leqc (l0 - l1) 0, Leqc (l1 - l0) 0]"

lemma constraint_to_le_constraint:
  assumes "constraint_to_le_constraint c = cs"
  shows "v \<Turnstile>\<^sub>c c \<longleftrightarrow> (\<forall> c' \<in> set cs. v \<Turnstile>\<^sub>l\<^sub>e c')"
  by (insert assms, cases c, auto simp: valuate_minus valuate_uminus)

(* It could be interesting to re-index variables so that there are all consecutive
   in the normalization operation. *)
definition normalize where
  "normalize cs = concat (map constraint_to_le_constraint cs)"

lemma normalize_satisfies: "v \<Turnstile>\<^sub>c\<^sub>s set cs \<longleftrightarrow> (\<forall> c \<in> set (normalize cs). v \<Turnstile>\<^sub>l\<^sub>e c)"
  unfolding normalize_def using constraint_to_le_constraint by auto

definition integral_linear_poly where "integral_linear_poly l = (\<forall> x. coeff l x \<in> \<int>)"
abbreviation "integral_constraint c \<equiv>
              (integral_linear_poly (lec_poly c) \<and> lec_const c \<in> \<int>)"
definition integral_constraints where
"integral_constraints cs = (\<forall> c \<in> set cs. integral_constraint c)"

primrec max_coeff :: "rat le_constraint \<Rightarrow> rat" where
"max_coeff (Le_Constraint _ l c) = Max ({\<bar>c\<bar>} \<union> {\<bar>coeff l x\<bar> | x. x \<in> vars l})"

lemma max_coeff_const: "max_coeff (Le_Constraint r l c) \<ge> \<bar>c\<bar>"
  using finite_vars by auto

lemma max_coeff: "max_coeff (Le_Constraint r l c) \<ge> \<bar>coeff l x\<bar>"
proof cases
  assume "x \<in> vars l"
  hence "\<bar>coeff l x\<bar> \<in> {\<bar>c\<bar>} \<union> {\<bar>coeff l x\<bar> | x. x \<in> vars l}" by blast
  thus ?thesis using finite_vars by simp
next
  assume "x \<notin> vars l" 
  hence "\<bar>coeff l x \<bar> = 0" using coeff_zero by auto
  also have "0 \<le> max_coeff (Le_Constraint r l c)"
    using max_coeff_const[of c r l] by linarith
  finally show ?thesis by blast
qed

lemma integral_max_coeff:
  assumes "integral_constraint c"
  shows "max_coeff c \<in> \<int>"
proof -
  obtain r l x where c: "c = Le_Constraint r l x"
    using le_constraint.collapse[of c] by metis

  have "max_coeff c \<in> {\<bar>x\<bar>} \<union> {\<bar>coeff l i\<bar> | i. i \<in> vars l}"
    unfolding c max_coeff.simps
    by (rule Max_in, insert finite_vars, simp_all)
  moreover have "{\<bar>x\<bar>} \<subseteq> \<int>" using assms unfolding c by auto
  moreover have "{\<bar>coeff l i\<bar> | i. i \<in> vars l} \<subseteq> \<int>"
    using assms unfolding c integral_linear_poly_def by auto
  ultimately show ?thesis by blast
qed

definition max_coeff_constraints where
"max_coeff_constraints cs = Max (set (0 # map max_coeff cs))"

lemma max_coeff_constraints_const:
  assumes "c \<in> set cs"
  shows "\<bar>lec_const c\<bar> \<le> max_coeff_constraints cs"
proof -
  have "\<bar>lec_const c\<bar> \<le> max_coeff c"
    using max_coeff_const le_constraint.collapse by metis
  moreover have "max_coeff c \<le> max_coeff_constraints cs"
    unfolding max_coeff_constraints_def using assms by auto
  ultimately show ?thesis by linarith
qed

lemma max_coeff_constraints:
  assumes "c \<in> set cs"
  shows "\<bar>coeff (lec_poly c) x\<bar> \<le> max_coeff_constraints cs"
proof -
  have "\<bar>coeff (lec_poly c) x\<bar> \<le> max_coeff c"
    using max_coeff le_constraint.collapse by metis
  moreover have "max_coeff c \<le> max_coeff_constraints cs"
    unfolding max_coeff_constraints_def using assms by auto
  ultimately show ?thesis by linarith
qed

definition constraints_to_pairs ::
  "rat le_constraint list \<Rightarrow> (linear_poly \<times> rat) list \<times> (linear_poly \<times> rat) list"
where "constraints_to_pairs cs =
  (let leq_cs = filter (\<lambda> c. lec_rel c = Leq_Rel) cs in
   let lt_cs = filter (\<lambda> c. lec_rel c = Lt_Rel) cs in
   (map (\<lambda> c. (lec_poly c, lec_const c)) leq_cs,
    map (\<lambda> c. (lec_poly c, lec_const c)) lt_cs))"

lemma constraints_to_pairs:
  assumes "constraints_to_pairs cs = (leq_pairs, lt_pairs)"
  shows "(\<forall> c \<in> set cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow> ((\<forall> (l, x) \<in> set leq_pairs. (l \<lbrace> v \<rbrace>) \<le> x) \<and>
                                       (\<forall> (l, x) \<in> set lt_pairs. (l \<lbrace> v \<rbrace>) < x))"
    (is "?L \<longleftrightarrow> ?R")
  and "integral_constraints cs \<Longrightarrow>
      (l, x) \<in> set leq_pairs \<union> set lt_pairs \<Longrightarrow> integral_linear_poly l \<and> x \<in> \<int>"
    (is "?INT0 \<Longrightarrow> ?LX \<Longrightarrow> ?INT1") 
  and "(l, x) \<in> set leq_pairs \<union> set lt_pairs \<Longrightarrow>
        \<bar>coeff l i\<bar> \<le> max_coeff_constraints cs \<and> \<bar>x\<bar> \<le> max_coeff_constraints cs"
    (is "?LX' \<Longrightarrow> ?BND")
proof -
  define leq_cs where "leq_cs = filter (\<lambda> c. lec_rel c = Leq_Rel) cs"
  define lt_cs where "lt_cs = filter (\<lambda> c. lec_rel c = Lt_Rel) cs"
  have "constraints_to_pairs cs = (map (\<lambda> c. (lec_poly c, lec_const c)) leq_cs,
                                   map (\<lambda> c. (lec_poly c, lec_const c)) lt_cs)"
    unfolding constraints_to_pairs_def leq_cs_def lt_cs_def
    by metis
  hence leq_pairs: "leq_pairs = map (\<lambda> c. (lec_poly c, lec_const c)) leq_cs"
     and lt_pairs: "lt_pairs = map (\<lambda> c. (lec_poly c, lec_const c)) lt_cs"
    using assms by auto
    

  have constructor: "\<And> c. c = Leq_Rel \<or> c = Lt_Rel"
  proof -
    fix c show "c = Leq_Rel \<or> c = Lt_Rel" by (cases c, simp_all)
  qed

  have "\<forall> c \<in> set leq_cs. lec_rel c = Leq_Rel" unfolding leq_cs_def by fastforce
  (* Why do automatic proving perform so bad on the following statement? Is there
     an infinite simplifications loop or something like that? *)
  hence leq_decomp: "\<forall> c \<in> set leq_cs. c = Le_Constraint Leq_Rel (lec_poly c) (lec_const c)"
    using leq_cs_def le_constraint.collapse by metis
  have "\<forall> c \<in> set lt_cs. lec_rel c = Lt_Rel" unfolding lt_cs_def by fastforce
  hence lt_decomp: "\<forall> c \<in> set lt_cs. c = Le_Constraint Lt_Rel (lec_poly c) (lec_const c)"
    using leq_cs_def le_constraint.collapse by metis

  have sets: "set cs = set leq_cs \<union> set lt_cs"
    unfolding leq_cs_def lt_cs_def using constructor by auto
  have "(\<forall> c \<in> set cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow>
        (\<forall> c \<in> set leq_cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<and> (\<forall> c \<in> set lt_cs. v \<Turnstile>\<^sub>l\<^sub>e c)"
    unfolding leq_cs_def lt_cs_def using constructor by auto
  also have "(\<forall> c \<in> set leq_cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow>
             (\<forall> c \<in> set leq_cs. ((lec_poly c) \<lbrace> v \<rbrace>) \<le> (lec_const c))"
    using leq_decomp satisfiable_le_constraint.simps[of v] rel_of.simps(1) by metis
  also have "(\<forall> c \<in> set lt_cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow>
             (\<forall> c \<in> set lt_cs. ((lec_poly c) \<lbrace> v \<rbrace>) < (lec_const c))"
    using lt_decomp satisfiable_le_constraint.simps[of v] rel_of.simps(2) by metis
  finally show "?L \<longleftrightarrow> ?R" unfolding leq_pairs lt_pairs by auto

  show "?INT0 \<Longrightarrow> ?LX \<Longrightarrow> ?INT1"
    unfolding integral_constraints_def leq_pairs lt_pairs sets
    by auto

  assume "?LX'"
  then obtain c where c: "c \<in> set cs"
                and l: "l = lec_poly c" and x: "x = lec_const c"
    unfolding leq_pairs lt_pairs sets by auto
  show ?BND
    unfolding l x
    using max_coeff_constraints[OF c, of i] max_coeff_constraints_const[OF c]
    by blast
qed

lift_definition vec_of_poly :: "linear_poly \<Rightarrow> nat \<Rightarrow> rat vec" is
  "\<lambda> l n. vec n l"
  .

lemma vec_of_poly_dim[simp]: "vec_of_poly v n \<in> carrier_vec n"
  by (transfer, auto)

lemma inverse_vec_of_poly:
  assumes "n > max_var l"
  shows "poly_of_vec (vec_of_poly l n) = l"
proof -
  have "\<forall> i \<ge> n. i \<notin> vars l" using assms max_var_max by fastforce
  thus ?thesis by (transfer, force)
qed

lemma dot_vec_of_poly:
  assumes v: "v \<in> carrier_vec n"
  assumes l: "n > Abstract_Linear_Poly.max_var l" 
  shows "(vec_of_poly l n) \<bullet> v = (l \<lbrace> val_of_vec v \<rbrace>)"
  using valuate_poly_of_vec[OF v, of "vec_of_poly l n"]
        inverse_vec_of_poly[OF l] by simp

lemma integral_vec_of_poly:
  "integral_linear_poly l \<Longrightarrow> vec_of_poly l n \<in> \<int>\<^sub>v"
  unfolding integral_linear_poly_def 
  by (transfer, auto simp: Ints_vec_def)


lemma vec_of_poly_bound:
  "\<forall> x. \<bar>coeff l x\<bar> \<le> Bnd \<Longrightarrow> vec_of_poly l n \<in> Bounded_vec Bnd"
  by (transfer, auto simp: Bounded_vec_def)

abbreviation "lec_max_var \<equiv> max_var \<circ> lec_poly"

definition constraints_max_var :: "rat le_constraint list \<Rightarrow> nat" where
"constraints_max_var cs = Max (set (0 # map lec_max_var cs))"

lemma constraints_max_var_to_pairs:
  assumes "constraints_to_pairs cs = (leq_pairs, lt_pairs)"
  assumes "(l, x) \<in> set leq_pairs \<union> set lt_pairs"
  shows "max_var l \<le> constraints_max_var cs"
proof -
  define leq_cs where "leq_cs = filter (\<lambda> c. lec_rel c = Leq_Rel) cs"
  define lt_cs where "lt_cs = filter (\<lambda> c. lec_rel c = Lt_Rel) cs"
  have "constraints_to_pairs cs = (map (\<lambda> c. (lec_poly c, lec_const c)) leq_cs,
                                   map (\<lambda> c. (lec_poly c, lec_const c)) lt_cs)"
    unfolding constraints_to_pairs_def leq_cs_def lt_cs_def
    by metis
  hence leq_pairs: "leq_pairs = map (\<lambda> c. (lec_poly c, lec_const c)) leq_cs"
     and lt_pairs: "lt_pairs = map (\<lambda> c. (lec_poly c, lec_const c)) lt_cs"
    using assms(1) by auto
  then obtain c where "c \<in> set cs" and "l = lec_poly c"
    using assms(2) unfolding leq_pairs lt_pairs leq_cs_def lt_cs_def by force
  moreover have "constraints_max_var cs = Max (set (0 # map lec_max_var cs))"
    unfolding constraints_max_var_def by presburger
  ultimately show ?thesis by simp
qed

definition mats_vecs_of_constraints ::
  "rat le_constraint list \<Rightarrow> rat mat \<times> rat vec \<times> rat mat \<times> rat vec" where
"mats_vecs_of_constraints cs = (
  let n = 1 + constraints_max_var cs in
  let (leq_pairs, lt_pairs) = constraints_to_pairs cs in
  let leq_polys = map fst leq_pairs in
  let leq_rows = map (\<lambda> l. vec_of_poly l n) leq_polys in
  let leq_bounds = map snd leq_pairs in
  let lt_polys = map fst lt_pairs in
  let lt_rows = map (\<lambda> l. vec_of_poly l n) lt_polys in
  let lt_bounds = map snd lt_pairs in
  (mat_of_rows n leq_rows, vec_of_list leq_bounds,
   mat_of_rows n lt_rows, vec_of_list lt_bounds))"

lemma satisfies_le_constraint_depend:
  assumes "n > lec_max_var c"
  and "\<forall> x < n. v0 x = v1 x"
shows "v0 \<Turnstile>\<^sub>l\<^sub>e c \<longleftrightarrow> v1 \<Turnstile>\<^sub>l\<^sub>e c"
proof -
  from assms have "\<forall> x \<in> vars (lec_poly c). v0 x = v1 x"
    using max_var_max[of _ "lec_poly c"] by force
  hence "((lec_poly c) \<lbrace> v0 \<rbrace>) = ((lec_poly c) \<lbrace> v1 \<rbrace>)"
    using valuate_depend by blast
  thus ?thesis
    using satisfiable_le_constraint.simps le_constraint.collapse by metis
qed

lemma satisfies_constraints_depend:
  assumes "n > constraints_max_var cs"
  and "\<forall> x < n. v0 x = v1 x"
shows "(\<forall> c \<in> set cs. v0 \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow> (\<forall> c \<in> set cs. v1 \<Turnstile>\<^sub>l\<^sub>e c)"
proof -
  have "constraints_max_var cs =  Max (set (0 # map lec_max_var cs))"
    unfolding constraints_max_var_def by presburger
  hence "\<And> c. c \<in> set cs \<Longrightarrow> lec_max_var c < n" using assms(1) by fastforce
  thus ?thesis using satisfies_le_constraint_depend[OF _ assms(2)] by blast
qed 

lemma mats_vecs_of_constraints:
  assumes "mats_vecs_of_constraints cs = (A, b, A', b')" 
   and n: "n = 1 + constraints_max_var cs"
  shows "\<exists> nr nr'. A \<in> carrier_mat nr n \<and>
                   b \<in> carrier_vec nr \<and>
                   A' \<in> carrier_mat nr' n \<and>
                   b' \<in> carrier_vec nr'" (is ?DIM)
   and "(\<forall> c \<in> set cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow> (A *\<^sub>v (vec n v) \<le> b \<and> A' *\<^sub>v (vec n v) <\<^sub>v b')"
     (is "?L \<longleftrightarrow> ?R")
   and "integral_constraints cs \<Longrightarrow> A \<in> \<int>\<^sub>m \<and> b \<in> \<int>\<^sub>v \<and> A' \<in> \<int>\<^sub>m \<and> b' \<in> \<int>\<^sub>v"
      (is "?INT0 \<Longrightarrow> ?INT1")
   and "A \<in> Bounded_mat (max_coeff_constraints cs) \<and>
        b \<in> Bounded_vec (max_coeff_constraints cs) \<and>
        A' \<in> Bounded_mat (max_coeff_constraints cs) \<and>
        b' \<in> Bounded_vec (max_coeff_constraints cs)" (is ?BNDS)
proof -
  obtain leq_pairs lt_pairs leq_polys lt_polys
         leq_rows leq_bounds lt_rows lt_bounds
         where
          pairs: "constraints_to_pairs cs = (leq_pairs, lt_pairs)" and
          leq_polys: "leq_polys = map fst leq_pairs" and
          leq_rows: "leq_rows = map (\<lambda> l. vec_of_poly l n) leq_polys" and
          leq_bounds: "leq_bounds = map snd leq_pairs" and
          lt_polys: "lt_polys = map fst lt_pairs" and
          lt_rows: "lt_rows = map (\<lambda> l. vec_of_poly l n) lt_polys" and
          lt_bounds: "lt_bounds = map snd lt_pairs" and
          res: "mats_vecs_of_constraints cs = (mat_of_rows n leq_rows,
                                               vec_of_list leq_bounds,
                                               mat_of_rows n lt_rows,
                                               vec_of_list lt_bounds)"
    unfolding mats_vecs_of_constraints_def
      apply(cases "constraints_to_pairs cs")
      apply(simp add: n del: vec_of_list_map)
      done
    from res assms(1) have A: "A = mat_of_rows n leq_rows" and
                           b: "b = vec_of_list leq_bounds" and
                           A': "A' = mat_of_rows n lt_rows" and
                           b': "b' = vec_of_list lt_bounds" by auto
  have A_carrier: "A \<in> carrier_mat (length leq_pairs) n" and
       b_carrier: "b \<in> carrier_vec (length leq_pairs)"
    using A b leq_rows leq_polys leq_bounds by (fastforce, fastforce)
  have A'_carrier: "A' \<in> carrier_mat (length lt_pairs) n" and
       b'_carrier: "b' \<in> carrier_vec (length lt_pairs)"
    using A' b' lt_rows lt_polys lt_bounds by (fastforce, fastforce)
  show ?DIM using A_carrier b_carrier A'_carrier b'_carrier by blast

  show "?L \<longleftrightarrow> ?R" proof(standard)
    assume v: ?L

    have "A *\<^sub>v (vec n v) \<le> b"
    proof (rule lesseq_vecI[OF _ b_carrier], insert A_carrier, simp)
      fix i
      assume i: "i < length leq_pairs"
      hence i': "i < dim_row A" using A leq_rows leq_polys by fastforce
      have pairs_i: "(leq_polys ! i, leq_bounds ! i) \<in> set leq_pairs"
        using i leq_polys leq_bounds by fastforce
      have max_var: "max_var (leq_polys ! i) < n" using n leq_polys
        using constraints_max_var_to_pairs[OF pairs, of "leq_polys ! i" "leq_bounds ! i"]
              pairs_i by force

      from v have "(\<forall> (l, x) \<in> set leq_pairs. (l \<lbrace> v \<rbrace>) \<le> x)"
        using constraints_to_pairs(1)[OF pairs] by blast
      hence "(leq_polys ! i) \<lbrace> v \<rbrace> \<le> leq_bounds ! i"
        using i leq_polys leq_bounds by auto
      also have "valuate (leq_polys ! i) v =
                 valuate (leq_polys ! i) (val_of_vec (vec n v))"
        unfolding val_of_vec_def
        apply(rule valuate_depend)
        apply(insert max_var max_var_max, force)
        done
      also have "\<dots> = vec_of_poly (leq_polys ! i) n \<bullet> (vec n v)"
        using dot_vec_of_poly[of "vec n v" n, OF _ max_var] by fastforce
      also have "vec_of_poly (leq_polys ! i) n = row A i"
        unfolding A leq_rows leq_polys
        using i length_map[of fst leq_pairs] by fastforce
      also have "row A i \<bullet> vec n v = (A *\<^sub>v (vec n v)) $ i"
        using index_mult_mat_vec[OF i'] by presburger
      also have "leq_bounds ! i = b $ i" unfolding b using i leq_bounds by fastforce
      finally show "(A *\<^sub>v (vec n v)) $ i \<le> b $ i" by blast
    qed

    moreover

    have "A' *\<^sub>v (vec n v) <\<^sub>v b'"
    proof (rule less_vecI[OF _ b'_carrier], insert A'_carrier, simp)
      fix i
      assume i: "i < length lt_pairs"
      hence i': "i < dim_row A'" using A' lt_rows lt_polys by force
      have pairs_i: "(lt_polys ! i, lt_bounds ! i) \<in> set lt_pairs"
        using i lt_polys lt_bounds by fastforce
      have max_var: "max_var (lt_polys ! i) < n" using n leq_polys
        using constraints_max_var_to_pairs[OF pairs] pairs_i by fastforce

      from v have "(\<forall> (l, x) \<in> set lt_pairs. (l \<lbrace> v \<rbrace>) < x)"
        using constraints_to_pairs(1)[OF pairs] by algebra
      hence "(lt_polys ! i) \<lbrace> v \<rbrace> < lt_bounds ! i"
        using i lt_polys lt_bounds by auto
      also have "valuate (lt_polys ! i) v =
                 valuate (lt_polys ! i) (val_of_vec (vec n v))"
        unfolding val_of_vec_def
        apply(rule valuate_depend)
        apply(insert max_var max_var_max, force)
        done
      also have "\<dots> = vec_of_poly (lt_polys ! i) n \<bullet> (vec n v)"
        using dot_vec_of_poly[of "vec n v" n, OF _ max_var] by fastforce
      also have "vec_of_poly (lt_polys ! i) n = row A' i"
        unfolding A' lt_rows lt_polys
        using i length_map[of fst lt_pairs] by fastforce
      also have "row A' i \<bullet> vec n v = (A' *\<^sub>v (vec n v)) $ i"
        using index_mult_mat_vec[OF i'] by presburger
      also have "lt_bounds ! i = b' $ i" unfolding b' using i lt_bounds by fastforce
      finally show "(A' *\<^sub>v (vec n v)) $ i < b' $ i" by blast
    qed
    ultimately show ?R by fastforce

  next 
    assume R: ?R
    define x where "x = vec n v"
    have xn: "x \<in> carrier_vec n" and x0: "A *\<^sub>v x \<le> b" and x1: "A' *\<^sub>v x <\<^sub>v b'"
      using R unfolding x_def by auto
  {
    fix l t
    assume lt0: "(l, t) \<in> set leq_pairs" 
    then obtain i where i: "i < length leq_pairs" and lt: "(l, t) = leq_pairs ! i"
      by (metis in_set_conv_nth)
    have max_var: "max_var l < n"
      using constraints_max_var_to_pairs[OF pairs, of l t] n lt0 by fastforce

    have "(A *\<^sub>v x) $ i \<le> b $ i" by (rule lesseq_vecD[OF b_carrier x0 i])
    also have "(A *\<^sub>v x) $ i = row A i \<bullet> x"
      by (rule index_mult_mat_vec, simp add: i A leq_rows leq_polys)
    also have "row A i = vec_of_poly l n"
      unfolding A leq_rows leq_polys
      using i length_map[of fst leq_pairs] lt fst_conv[of l t] by simp
    also have "vec_of_poly l n \<bullet> x = (l \<lbrace> val_of_vec x \<rbrace>)"
      by (rule dot_vec_of_poly[OF xn max_var])
    also have "b $ i = t" unfolding b leq_bounds using i lt
      using snd_conv[of l t] vec_of_list_index by simp
    finally have "(l \<lbrace> val_of_vec x \<rbrace>) \<le> t" by blast
  } moreover {
    fix l t
    assume lt0: "(l, t) \<in> set lt_pairs" 
    then obtain i where i: "i < length lt_pairs" and lt: "(l, t) = lt_pairs ! i"
      by (metis in_set_conv_nth)
    have max_var: "max_var l < n"
      using constraints_max_var_to_pairs[OF pairs, of l t] n lt0 by fastforce

    have "(A' *\<^sub>v x) $ i < b' $ i"
      by (rule less_vecD[OF x1 b'_carrier i])
    also have "(A' *\<^sub>v x) $ i = row A' i \<bullet> x"
      by (rule index_mult_mat_vec, simp add: i A' lt_rows lt_polys)
    also have "row A' i = vec_of_poly l n"
      unfolding A' lt_rows lt_polys
      using i length_map[of fst lt_pairs] lt fst_conv[of l t] by simp
    also have "vec_of_poly l n \<bullet> x = (l \<lbrace> val_of_vec x \<rbrace>)"
      by (rule dot_vec_of_poly[OF xn max_var])
    also have "b' $ i = t" unfolding b' lt_bounds using i lt
      using snd_conv[of l t] vec_of_list_index by simp
    finally have "(l \<lbrace> val_of_vec x \<rbrace>) < t" by blast
  }
  ultimately have
    "(\<forall>(l, t)\<in>set leq_pairs. (l \<lbrace> val_of_vec x \<rbrace>) \<le> t) \<and>
     (\<forall>(l, t)\<in>set lt_pairs. (l \<lbrace> val_of_vec x \<rbrace>) < t)" by blast
  hence "\<forall> c \<in> set cs. val_of_vec x \<Turnstile>\<^sub>l\<^sub>e c"
    using constraints_to_pairs(1)[OF pairs] by presburger
  thus ?L  using satisfies_constraints_depend[of cs n v "val_of_vec x"] n
    unfolding x_def val_of_vec_def by fastforce
  qed

  have leq_rows_carrier: "set leq_rows \<subseteq> carrier_vec n" unfolding leq_rows by auto
  have lt_rows_carrier: "set lt_rows \<subseteq> carrier_vec n" unfolding lt_rows by auto

  let ?Bnd = "max_coeff_constraints cs" 
  from constraints_to_pairs(3)[OF pairs]
  have polys: "\<forall> l \<in> set leq_polys \<union> set lt_polys. \<forall> i. \<bar>coeff l i\<bar> \<le> ?Bnd"
   and bounds: "\<forall> c \<in> set leq_bounds \<union> set lt_bounds. \<bar>c\<bar> \<le> ?Bnd"
    unfolding leq_polys lt_polys leq_bounds lt_bounds by (force, force)
  from polys have "set leq_rows \<union> set lt_rows \<subseteq> Bounded_vec ?Bnd"
    unfolding leq_rows lt_rows
    using vec_of_poly_bound[of _ _ n] by auto
  hence "A \<in> Bounded_mat ?Bnd \<and> A' \<in> Bounded_mat ?Bnd"
    using Bounded_vec_rows_Bounded_mat[of _ ?Bnd]
          rows_mat_of_rows[OF leq_rows_carrier]
          rows_mat_of_rows[OF lt_rows_carrier]
    unfolding A A' by fastforce
  moreover have "b \<in> Bounded_vec ?Bnd \<and> b' \<in> Bounded_vec ?Bnd"
    by(auto simp: b b' Bounded_vec_def bounds)
  ultimately show ?BNDS by blast

  assume int0: ?INT0
  from constraints_to_pairs(2)[OF pairs int0]
  have polys: "\<forall> l \<in> set leq_polys \<union> set lt_polys. integral_linear_poly l"
   and bounds: "set leq_bounds \<union> set lt_bounds \<subseteq> \<int>"
    unfolding leq_polys lt_polys leq_bounds lt_bounds
    by (force, force)

  from polys have "set leq_rows \<union> set lt_rows \<subseteq> \<int>\<^sub>v"
    unfolding leq_rows lt_rows using integral_vec_of_poly[of _ n] by auto
  hence "A \<in> \<int>\<^sub>m \<and> A' \<in> \<int>\<^sub>m" unfolding A A'
    using Ints_vec_rows_Ints_mat rows_mat_of_rows[OF leq_rows_carrier]
                                 rows_mat_of_rows[OF lt_rows_carrier] by fastforce
  moreover have "b \<in> \<int>\<^sub>v \<and> b' \<in> \<int>\<^sub>v" unfolding b b' Ints_vec_def
    using bounds by fastforce
  ultimately show ?INT1 by blast
qed

primrec mul_constraint where
"mul_constraint x (Le_Constraint r l c) = Le_Constraint r (x *R l) (x * c)"

lemma mul_constraint:
  assumes "x > 0"
  shows "v \<Turnstile>\<^sub>l\<^sub>e c \<longleftrightarrow> v \<Turnstile>\<^sub>l\<^sub>e mul_constraint x c"
proof -
  from le_constraint.collapse[of c] obtain r l y where
    decomp: "c = Le_Constraint r l y"
    by metis
  have "(l \<lbrace> v \<rbrace>) < y \<longleftrightarrow> ((x *R l) \<lbrace> v \<rbrace>) < x * y"
    using mult_less_cancel_left_pos[OF assms] valuate_scaleRat[of x l v]
    by force
  moreover have "(l \<lbrace> v \<rbrace>) \<le> y \<longleftrightarrow> ((x *R l) \<lbrace> v \<rbrace>) \<le> x * y"
    using mult_le_cancel_left_pos[OF assms] valuate_scaleRat[of x l v]
    by force
  ultimately show ?thesis unfolding decomp
    by (cases r, simp_all)
qed

primrec common_denominator where
"common_denominator (Le_Constraint _ l c) =
  (let coeffs_list = map (coeff l) (vars_list l) in
   let denominators = map (snd \<circ> quotient_of) (c # coeffs_list) in
   lcm_list denominators)"

lemma mult_denom_int:
  assumes "quotient_of x = (n, d)"
  and "d dvd d'"
  shows "of_int d' * x \<in> \<int>"
proof -
  from assms(2) obtain k where d': "d' = k * d" unfolding dvd_def by fastforce
  have "d \<noteq> 0" using assms quotient_of_nonzero(2)[of x] by auto
  hence "of_int n = of_int d * x" using quotient_of_div[OF assms(1)] by simp
  hence "of_int d * x \<in> \<int>" using Ints_of_int by metis
  hence "of_int k * (of_int d * x) \<in> \<int>" by simp
  hence "(of_int k * of_int d) * x \<in> \<int>" using mult.assoc by metis
  thus ?thesis unfolding d' by simp
qed

lemma common_denominator:
  shows "common_denominator c > 0" (is ?pos)
   and "of_int (common_denominator c) * lec_const c \<in> \<int>" (is ?const)
   and "of_int (common_denominator c) * (coeff (lec_poly c) i) \<in> \<int>"
     (is ?coeff)
proof -
  from le_constraint.collapse[of c] obtain r l x where
    decomp: "c = Le_Constraint r l x"
    by metis
  define coeffs_list where "coeffs_list = map (coeff l) (vars_list l)"
  define denominators where "denominators = map (snd \<circ> quotient_of) (x # coeffs_list)"
  have res: "common_denominator c = lcm_list denominators"
    unfolding decomp denominators_def coeffs_list_def common_denominator.simps
    by presburger

  have "0 \<notin> set denominators"
    unfolding denominators_def using quotient_of_nonzero(2) by fastforce
  thus ?pos using res list_lcm_pos(3) by presburger

  have "snd (quotient_of x) dvd common_denominator c"
    using list_lcm unfolding res denominators_def by auto
  thus ?const
    using mult_denom_int[OF surjective_pairing]
    unfolding decomp le_constraint.sel(3) by blast

  show ?coeff
  proof cases
    assume "i \<in> vars l"
    hence "coeff l i \<in> set coeffs_list" 
      unfolding coeffs_list_def using set_vars_list by auto
    hence "snd (quotient_of (coeff l i)) dvd common_denominator c"
      using list_lcm unfolding res denominators_def by auto
    thus ?coeff
    using mult_denom_int[OF surjective_pairing]
    unfolding decomp le_constraint.sel(2) by blast
  next
    assume "i \<notin> vars l"
    hence "coeff l i = 0" using coeff_zero by fast
    thus ?coeff unfolding decomp le_constraint.sel(2) by auto
  qed
qed

definition
"constraint_to_ints c = mul_constraint (rat_of_int (common_denominator c)) c"

lemma constraint_to_ints: fixes c :: "rat le_constraint"
  shows "v \<Turnstile>\<^sub>l\<^sub>e c \<longleftrightarrow> v \<Turnstile>\<^sub>l\<^sub>e constraint_to_ints c" (is ?R0)
  and "integral_constraint (constraint_to_ints c)" (is ?R1)
proof -
  show ?R0
    using common_denominator(1) mul_constraint
    unfolding constraint_to_ints_def by presburger
    
  let ?x = "of_int (common_denominator c)"
  have "c = Le_Constraint (lec_rel c) (lec_poly c) (lec_const c)"
    using le_constraint.collapse by auto
  hence "mul_constraint ?x c =
         Le_Constraint (lec_rel c) (?x *R lec_poly c) (?x * lec_const c)"
    using mul_constraint.simps by metis
  hence "lec_poly (mul_constraint ?x c) = ?x *R lec_poly c"
   and "lec_const (mul_constraint ?x c) = ?x * lec_const c" by auto
  thus ?R1 using common_denominator(2-3) unfolding integral_linear_poly_def
unfolding constraint_to_ints_def
    by simp
qed
 
definition compute_bound :: "constraint list \<Rightarrow> int" where
"compute_bound cs =
  (let le_cs = normalize cs in
   let le_cs' = map constraint_to_ints le_cs in
   let max_coeff = max_coeff_constraints le_cs' in
   let n = 1 + constraints_max_var le_cs' in
   fact (n + 1) * (max 1 \<lfloor>max_coeff\<rfloor>) ^ n)"

lemma compute_bound:
  assumes "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, I)"
  shows "\<exists> v. v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, I) \<and> (\<forall> i \<in> I. \<bar>v i\<bar> \<le> of_int (compute_bound cs))"
proof -
  define le_cs where "le_cs = normalize cs"
  define le_cs' where "le_cs' = map constraint_to_ints le_cs"
  define max_cf where "max_cf = max_coeff_constraints le_cs'"
  define n where "n = 1 + constraints_max_var le_cs'"
  define Bnd where "Bnd = fact (n + 1) * (max 1 \<lfloor>max_cf\<rfloor>) ^ n"
  have id: "compute_bound cs = Bnd"
    unfolding compute_bound_def le_cs_def le_cs'_def
              max_cf_def n_def Bnd_def by metis

  interpret gram_schmidt_floor n .

  have int: "integral_constraints le_cs'"
    unfolding le_cs'_def integral_constraints_def
    using constraint_to_ints(2) by auto
  hence "max_cf \<in> \<int>"
    unfolding max_cf_def integral_constraints_def
              max_coeff_constraints_def
    using integral_max_coeff Max_in[of "set (0 # map max_coeff le_cs')"]
    by fastforce
  hence "of_int \<lfloor>max_cf\<rfloor> = max_cf" using floor_of_int_eq by blast
  hence "of_int (max 1 \<lfloor>max_cf\<rfloor>) = max 1 max_cf" by linarith
  hence Bnd_rat: "of_int Bnd = fact (n + 1) * (max 1 max_cf) ^ n"
    unfolding Bnd_def by simp

  have "rat_of_int Bnd \<ge> 0" unfolding Bnd_def by fastforce

  obtain A b A' b' where matsvecs: "mats_vecs_of_constraints le_cs' = (A, b, A', b')"
    by (rule prod_cases4)
  obtain nr nr' where
    A_dim: "A \<in> carrier_mat nr n" and b_dim: "b \<in> carrier_vec nr" and
    A'_dim: "A' \<in> carrier_mat nr' n" and b'_dim: "b' \<in> carrier_vec nr'"
    using mats_vecs_of_constraints(1)[OF matsvecs n_def] by blast

  from mats_vecs_of_constraints(3-4)[OF matsvecs n_def] int
  have A: "A \<in> \<int>\<^sub>m \<inter> Bounded_mat max_cf"
   and A': "A' \<in> \<int>\<^sub>m \<inter> Bounded_mat max_cf"
   and b: "b \<in> \<int>\<^sub>v \<inter> Bounded_vec max_cf"
   and b': "b' \<in> \<int>\<^sub>v \<inter> Bounded_vec max_cf"
    unfolding max_cf_def by auto
  {
    fix v
    have "v \<Turnstile>\<^sub>c\<^sub>s set cs \<longleftrightarrow> (\<forall> c \<in> set le_cs. v \<Turnstile>\<^sub>l\<^sub>e c)"
      unfolding le_cs_def by (rule normalize_satisfies)
    also have "\<dots> \<longleftrightarrow> (\<forall> c \<in> set le_cs'. v \<Turnstile>\<^sub>l\<^sub>e c)"
      unfolding le_cs'_def using constraint_to_ints(1) by auto
    also have "\<dots> \<longleftrightarrow> (A *\<^sub>v vec n v \<le> b \<and> A' *\<^sub>v vec n v <\<^sub>v b')"
      by (rule mats_vecs_of_constraints(2)[OF matsvecs n_def])
    finally have "v \<Turnstile>\<^sub>c\<^sub>s set cs \<longleftrightarrow> (A *\<^sub>v vec n v \<le> b \<and> A' *\<^sub>v vec n v <\<^sub>v b')"
      by blast
  } note sat_cs = this
  hence Avb: "A *\<^sub>v vec n v \<le> b" and A'vb': "A' *\<^sub>v vec n v <\<^sub>v b'" using assms by auto
  from assms have "vec n v \<in> indexed_Ints_vec I"
    unfolding indexed_Ints_vec_def by auto
  then obtain x where xn: "x \<in> carrier_vec n" and xI: "x \<in> indexed_Ints_vec I"
                       and Axb: "A *\<^sub>v x \<le> b" and A'xb': "A' *\<^sub>v x <\<^sub>v b'"
                       and xBnd: "x \<in> Bounded_vec (of_int Bnd)"
    
    using small_mixed_integer_solution[OF A_dim A'_dim b_dim b'_dim
                                          A b A' b' _ _ Avb A'vb']
    unfolding Bnd_rat max_cf_def
    by auto

  define v' where "v' = (\<lambda> i. if i < n then x $ i else 0)"
  have "vec n v' = x" unfolding v'_def using xn by fastforce
  hence "v' \<Turnstile>\<^sub>c\<^sub>s set cs"
    using sat_cs Axb A'xb' by presburger
  moreover have "\<forall> i \<in> I. v' i \<in> \<int>"
    using xI xn unfolding v'_def indexed_Ints_vec_def by fastforce
  moreover have "\<forall> i. \<bar>v' i\<bar> \<le> of_int Bnd"
  proof (rule allI, cases)
    fix i assume "i < n"
    thus "\<bar>v' i\<bar> \<le> of_int Bnd"
      using xBnd xn unfolding v'_def Bounded_vec_def by fastforce
  next
    fix i assume "\<not> (i < n)"
    thus "\<bar>v' i\<bar> \<le> of_int Bnd" unfolding v'_def using `of_int Bnd \<ge> 0` by fastforce
  qed
  ultimately show ?thesis unfolding id by auto
qed

definition branch_and_bound :: "constraint list \<Rightarrow> var list \<Rightarrow> rat valuation option"
where "branch_and_bound cs Is = (
  let Bnd = compute_bound cs in
  branch_and_bound_core cs Is (\<lambda> _. -Bnd) (\<lambda> _. Bnd))"

lemma branch_and_bound_sat:
  "branch_and_bound cs Is = Some v \<Longrightarrow> v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, set Is)"
  unfolding branch_and_bound_def using branch_and_bound_core_sat by metis

lemma branch_and_bound_unsat:
  assumes "branch_and_bound cs Is = None"
  shows "\<not> v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, set Is)"
proof
  define Bnd where "Bnd = compute_bound cs"
  assume "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, set Is)"
  then obtain v where v: "v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set cs, set Is)"
                 and vBnd: "(\<forall> i \<in> set Is. \<bar>v i\<bar> \<le> of_int Bnd)"
    using compute_bound unfolding Bnd_def by blast

  
  from assms have "branch_and_bound_core cs Is (\<lambda> _. -Bnd) (\<lambda> _. Bnd) = None"
    unfolding branch_and_bound_def Bnd_def by meson
  moreover from vBnd have "(\<forall> i \<in> set Is. of_int (-Bnd) \<le> v i \<and> v i \<le> of_int Bnd)"
    by fastforce
  ultimately show False
    using branch_and_bound_core_unsat v by presburger
qed

hide_const (open) Var
hide_const (open) max_var
hide_const (open) vars_list

end
