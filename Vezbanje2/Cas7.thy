theory Cas7
  imports Main

begin

lemma 
  fixes n::nat 
  shows "(3::nat) dvd ((5::nat)^n + 2^(n+1))"
proof (induction n)
  case 0
  then show ?case by (simp add: numeral_Bit1)
next
  case (Suc n)
  then obtain k::nat where IH: "(5::nat)^n + 2^(n+1) = 3*k" by (auto simp add: algebra_simps)
  have "(5::nat)^(Suc n) + 2^(Suc n + 1) = (5::nat)^(n+1) + 2^(n + 1 + 1)" by (auto simp add: algebra_simps)
  also have "... = (5::nat)^(n+1) + 2^(n+2)" by (auto simp add: algebra_simps)
  also have "... = 5 * (5::nat)^n + 2^(n+2)" by (auto simp add: algebra_simps)
  also have "... = 5 * ((5::nat)^n + 2^(n+1) - 2^(n+1)) + 2^(n+2)" by (auto simp add: algebra_simps)
  also have "... = 5 * ((5::nat)^n + 2^(n+1)) - 5 * 2^(n+1) + 2^(n+2)" by (auto simp add: algebra_simps)
  also have "... = (5::nat) * (3 * k) - 5 * 2^(n+1) + 2 * 2^(n+1)" using IH by (auto simp add: algebra_simps)
  also have "... = (5::nat) * 3 * k - 3 * 2^(n+1)" using IH by (auto simp add: algebra_simps)
  also have "... = (3::nat) * (5 * k - 2^(n+1))" using IH by (auto simp add: algebra_simps)
  also have "... = (3::nat) * (5 * k - 2^(Suc n))" using IH by (auto simp add: algebra_simps)
  finally show ?case using IH by (auto simp add: algebra_simps)
qed



end