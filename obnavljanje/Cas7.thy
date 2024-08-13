theory Cas7
  imports Main

begin

primrec suma :: "nat \<Rightarrow> int" 
  where "suma 0 = 0"
  | "suma (Suc n) = suma n + (-1)^(Suc n) * (2* int(Suc n) - 1)"

value "suma 6"

lemma "suma n = (-1)^n * (int n)"
  by (induction n) (auto simp add: algebra_simps)

lemma "suma n = (-1)^n * (int n)"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have "suma (Suc n) = suma n + (-1)^(Suc n) * (2 * int(Suc n) - 1)" by auto
  also have "... = (-1)^n * (int n) + (-1)^(Suc n) * (2 * int(Suc n) - 1)" using Suc by auto
  also have "... = (-1)^(Suc n) * 2 * int(Suc n) - (-1)^(Suc n) - (-1)^(Suc n) * int(n)" by (simp add: algebra_simps)
  also have "... = (-1)^(Suc n) * 2 * int(Suc n) - (-1)^(Suc n) * int(Suc n)" by (simp add: algebra_simps)
  also have "... = (-1)^(Suc n) * (2 * int(Suc n) - int(Suc n))" by (simp add: algebra_simps)
  also have "... = (-1)^(Suc n) * int(Suc n)" by (simp add: algebra_simps)
  finally show ?case .
qed


end