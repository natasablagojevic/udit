theory Cas6 
  imports Main

begin 

definition three :: "nat" where "three = 3"

(*relacije*)

(*
lemma 
  assumes sim: "\<forall> x y. \<rho> x y \<longrightarrow> \<rho> y x" and 
          trans: "\<forall> x y z. \<rho> x y \<and> \<rho> y z \<longrightarrow> \<rho> x z" and 
          ex: "\<forall> x. \<exists> y. \<rho> x y"
  shows "\<forall> x. \<rho> x x"
proof 
  fix x 
  obtain y where "\<rho> x y"
    using ex 
    by auto 

  moreover

  then have "\<rho> x y \<longrightarrow> \<rho> y x"
    using sim 
    by auto 

  ultimately

  then have ""

  show "\<rho> x x"
    by auto
qed
*)

lemma 
  fixes x y :: real
  shows "(x + y)^2 = x^2 + 2*x*y + y^2"
proof-
  have "(x + y)^2 = (x + y)*(x + y)"
    unfolding power2_eq_square 
    by (rule refl)

  thm algebra_simps (* osnovne algebarske manipulacije *)

  find_theorems "_ * (_ + _) = _ * _ + _ * _"

  also have "... = (x + y) * x + (x + y) * y"
   (* by (auto simp add: field_simps)*) (* distrib_left  *) (* apply subst distrib_left  *)
    by (subst distrib_left, rule refl)

  also have "... = (x*x + y*x) + (x*y + y*y)"
    apply (subst distrib_right)
    apply (subst distrib_right)
    apply (rule refl)
    done

  also have "... = x*x + (y*x + x*y) + y*y"
    apply (subst add.assoc[symetric])
    apply (subst add.assoc)
    apply (rule refl)
    done

  also have "... = x*x + (x*y + x*y) + y*y"
    thm mult.commute[where a=y and b=x]
    apply (subst mult.commute[where a=y and b=x, symetric])
    apply (rule refl)
    done 

  also have "... = x*x + (2*x*y) + y*y"
    apply (subst mult_2[symetric])
    apply (subst mult.assoc[of 2])
    apply (rule refl)
    done 

  also have "... = x^2 + 2*x*y + y^2"
    apply (subst power2_eq_square[symetric])
    apply (subst power2_eq_square[symetric])
    apply (rule refl)
    done

  finally

  show ?thesis
    . 


qed 



end