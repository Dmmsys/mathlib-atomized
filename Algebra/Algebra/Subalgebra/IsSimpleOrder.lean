/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
If `A` is a domain, and a finite-dimensional algebra over a field `F`, with prime dimension,
then there are no non-trivial `F`-subalgebras.
-/

public section

open Module Submodule

/-
**Subalgebra.isSimpleOrder_of_finrank_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.isSimpleOrder_of_finrank_prime (F A) [Field F] [Ring A] [IsDoma
in A] [Algebra F A] (hp : (finrank F A).Prime) : IsSimpleOrder (Subalgebra F A)
参数：F A；hp : (finrank F A).Prime。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_one`：¬Nat.Prime 1
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subalgebra.bot_eq_top_iff_finrank_eq_one`：bot_eq_top_iff_finrank_eq_one 
[Nontrivial E] [Module.Free F E] : (⊥ : Subalgebra F E) = ⊤ ↔ finrank F E = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `FiniteDimensional.of_finrank_pos`：of_finrank_pos (h : 0 < finrank K V) :
 FiniteDimensional K V
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Subalgebra.eq_bot_of_finrank_one`：eq_bot_of_finrank_one (h : finrank F S
 = 1) [Module.Free F S] : S = ⊥
· 使用定理 `Algebra.toSubmodule_eq_top`：toSubmodule_eq_top {S : Subalgebra R A} : Su
balgebra.toSubmodule S = ⊤ ↔ S = ⊤
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subalgebra.finrank_toSubmodule`：Subalgebra.finrank_toSubmodule (S : Suba
lgebra F E) : finrank F (Subalgebra.toSubmodule S) = finrank F S
· 使用定理 `Nat.Prime.eq_one_or_self_of_dvd`：∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣
 p → m = 1 ∨ m = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `Subalgebra.isScalarTower_mid`：∀ {R : Type u} {A : Type v} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {α
 : Type u_1} {β : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
-/
theorem Subalgebra.isSimpleOrder_of_finrank_prime (F A) [Field F] [Ring A] [IsDomain A]
    [Algebra F A] (hp : (finrank F A).Prime) : IsSimpleOrder (Subalgebra F A) :=
  { toNontrivial :=
      ⟨⟨⊥, ⊤, fun he =>
          Nat.not_prime_one ((Subalgebra.bot_eq_top_iff_finrank_eq_one.1 he).subst hp)⟩⟩
    eq_bot_or_eq_top := fun K => by
      have : FiniteDimensional _ _ := .of_finrank_pos hp.pos
      let := divisionRingOfFiniteDimensional F K
      refine (hp.eq_one_or_self_of_dvd _ ⟨_, (finrank_mul_finrank F K A).symm⟩).imp ?_ fun h => ?_
      · exact fun h' => Subalgebra.eq_bot_of_finrank_one h'
      · exact
          Algebra.toSubmodule_eq_top.1 (eq_top_of_finrank_eq <| K.finrank_toSubmodule.trans h) }
-- TODO: `IntermediateField` version
