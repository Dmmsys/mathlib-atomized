/-
Copyright (c) 2019 Kenny Lau, Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Jujian Zhang
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Data.Finset.Order
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Tactic.SuppressCompilation

/-!
# Direct limit of rings, and fields

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable rings or fields.

It is constructed as a quotient of the free commutative ring instead of a quotient of
the disjoint union so as to make the operations (addition etc.) "computable".

## Main definition

* `Ring.DirectLimit G f`

-/

@[expose] public section

assert_not_exists Cardinal

suppress_compilation
noncomputable section -- needed for `deriving`

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

open Submodule

namespace Ring

variable [∀ i, CommRing (G i)]

section

variable (f : ∀ i j, i ≤ j → G i → G j)

open FreeCommRing

/-- The direct limit of a directed system is the ring obtained by gluing the components along the
maps. -/
/-
**Ring.DirectLimit** 是 Mathlib 中的一个定义，位于命名空间 `Ring`。
形式化陈述：DirectLimit : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direct limit of a directed system is the ring obtained by gluing the compone
nts along the
maps.
-/
def DirectLimit : Type _ :=
  FreeCommRing (Σ i, G i) ⧸
    Ideal.span
      { a |
        (∃ i j H x, of (⟨j, f i j H x⟩ : Σ i, G i) - of ⟨i, x⟩ = a) ∨
          (∃ i, of (⟨i, 1⟩ : Σ i, G i) - 1 = a) ∨
            (∃ i x y, of (⟨i, x + y⟩ : Σ i, G i) - (of ⟨i, x⟩ + of ⟨i, y⟩) = a) ∨
              ∃ i x y, of (⟨i, x * y⟩ : Σ i, G i) - of ⟨i, x⟩ * of ⟨i, y⟩ = a }
deriving Zero, One, AddCommMonoid, Ring, CommRing, Inhabited

namespace DirectLimit

/-- The canonical map from a component to the direct limit. -/
nonrec def of (i) : G i →+* DirectLimit G f :=
  RingHom.mk'
    { toFun := fun x ↦ Ideal.Quotient.mk _ (of (⟨i, x⟩ : Σ i, G i))
      map_one' := Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inl ⟨i, rfl⟩
      map_mul' := fun x y ↦
        Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inr <| Or.inr ⟨i, x, y, rfl⟩ }
    fun x y ↦ Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inr <| Or.inl ⟨i, x, y, rfl⟩

variable {G f}

/-
**Ring.DirectLimit.quotientMk_of** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：quotientMk_of (i x) : Ideal.Quotient.mk _ (.of ⟨i, x⟩) = of G f i x
参数：i x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotientMk_of (i x) : Ideal.Quotient.mk _ (.of ⟨i, x⟩) = of G f i x :=
  rfl
/-
**Ring.DirectLimit.of_f** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：∀ {ι : Type u_1} [inst : Preorder ι] {G : ι → Type u_2} [inst_1 : (i : ι) 
→ CommRing (G i)]   {f : (i j : ι) → i ≤ j → G i → G j} {i j : ι} (hij : i ≤ j) 
(x : G i),   (Ring.DirectLimit.of G f j) (f i j hij x) = (Ring.DirectLimit.of G 
f i) x
参数：i : ι；G i；i j : ι；hij : i ≤ j；x : G i；Ring.DirectLimit.of G f j；f i j hij x；R
ing.DirectLimit.of G f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
@[simp] theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
  Ideal.Quotient.eq.2 <| subset_span <| Or.inl ⟨i, j, hij, x, rfl⟩

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
/-
**Ring.DirectLimit.exists_of** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：exists_of [Nonempty ι] [IsDirectedOrder ι] (z : DirectLimit G f) : exists 
i x, of G f i x = z
参数：z : DirectLimit G f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `FreeCommRing.induction_on`：∀ {α : Type u} {motive : FreeCommRing α → Pro
p} (z : FreeCommRing α),   motive (-1) →     (∀ (b : α), motive (FreeCommRing.of
 b)) →       (∀…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `Ring.DirectLimit.of_f`：∀ {ι : Type u_1} [inst : Preorder ι] {G : ι → Typ
e u_2} [inst_1 : (i : ι) → CommRing (G i)]   {f : (i j : ι) → i ≤ j → G i → G j}
 {i j : ι} …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …

--- 原说明 ---
Every element of the direct limit corresponds to some element in
some component of the directed system.
-/
theorem exists_of [Nonempty ι] [IsDirectedOrder ι] (z : DirectLimit G f) :
    ∃ i x, of G f i x = z := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine z.induction_on ⟨Classical.arbitrary ι, -1, by simp; rfl⟩ (fun ⟨i, x⟩ ↦ ⟨i, x, rfl⟩) ?_ ?_
    <;> rintro x' y' ⟨i, x, hx⟩ ⟨j, y, hy⟩ <;> have ⟨k, hik, hjk⟩ := exists_ge_ge i j
  · exact ⟨k, f i k hik x + f j k hjk y, by rw [map_add, of_f, of_f, hx, hy]; rfl⟩
  · exact ⟨k, f i k hik x * f j k hjk y, by rw [map_mul, of_f, of_f, hx, hy]; rfl⟩

section

open Polynomial

variable {f' : ∀ i j, i ≤ j → G i →+* G j}

nonrec theorem Polynomial.exists_of [Nonempty ι] [IsDirectedOrder ι]
    (q : Polynomial (DirectLimit G fun i j h ↦ f' i j h)) :
    ∃ i p, Polynomial.map (of G (fun i j h ↦ f' i j h) i) p = q :=
  Polynomial.induction_on q
    (fun z ↦
      let ⟨i, x, h⟩ := exists_of z
      ⟨i, C x, by rw [map_C, h]⟩)
    (fun q₁ q₂ ⟨i₁, p₁, ih₁⟩ ⟨i₂, p₂, ih₂⟩ ↦
      let ⟨i, h1, h2⟩ := exists_ge_ge i₁ i₂
      ⟨i, p₁.map (f' i₁ i h1) + p₂.map (f' i₂ i h2), by
        rw [Polynomial.map_add, map_map, map_map, ← ih₁, ← ih₂]
        congr 2 <;> ext x <;> simp_rw [RingHom.comp_apply, of_f]⟩)
    fun n z _ ↦
    let ⟨i, x, h⟩ := exists_of z
    ⟨i, C x * X ^ (n + 1), by rw [Polynomial.map_mul, map_C, h, Polynomial.map_pow, map_X]⟩

end

@[elab_as_elim]
/-
**Ring.DirectLimit.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：induction_on [Nonempty ι] [IsDirectedOrder ι] {C : DirectLimit G f -> Prop
} (z : DirectLimit G f) (ih : forall i x, C (of G f i x)) : C z
参数：z : DirectLimit G f；ih : forall i x, C (of G f i x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.DirectLimit.exists_of`：exists_of [Nonempty ι] [IsDirectedOrder ι] (
z : DirectLimit G f) : exists i x, of G f i x = z
-/
theorem induction_on [Nonempty ι] [IsDirectedOrder ι] {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of G f i x)) : C z :=
  let ⟨i, x, hx⟩ := exists_of z
  hx ▸ ih i x

variable (P : Type*) [CommRing P]

open FreeCommRing

variable (G f) in
/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
/-
**Ring.DirectLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 `Ring.DirectLimit`。
形式化陈述：lift (g : forall i, G i ->+* P) (Hg : forall i j hij x, g j (f i j hij x) 
= g i x) : DirectLimit G f ->+* P
参数：g : forall i, G i ->+* P；Hg : forall i j hij x, g j (f i j hij x) = g i x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of the direct limit: maps from the components to another 
ring
that respect the directed system structure (i.e. make some diagram commute) give
 rise
to a unique map out of the direct limit.
-/
def lift (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →+* P :=
  Ideal.Quotient.lift _ (FreeCommRing.lift fun x : Σ i, G i ↦ g x.1 x.2)
    (by
      suffices Ideal.span _ ≤
          Ideal.comap (FreeCommRing.lift fun x : Σ i : ι, G i ↦ g x.fst x.snd) ⊥ by
        intro x hx
        exact (mem_bot P).1 (this hx)
      rw [Ideal.span_le]
      intro x hx
      rw [SetLike.mem_coe, Ideal.mem_comap, mem_bot]
      rcases hx with (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩) <;>
        simp only [map_sub, lift_of, Hg, map_one, map_add, map_mul,
          (g i).map_one, (g i).map_add, (g i).map_mul, sub_self])

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
/-
**Ring.DirectLimit.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：∀ {ι : Type u_1} [inst : Preorder ι] {G : ι → Type u_2} [inst_1 : (i : ι) 
→ CommRing (G i)]   {f : (i j : ι) → i ≤ j → G i → G j} (P : Type u_3) [inst_2 :
 CommRing P] (g : (i : ι) → G i →+* P)   (Hg : ∀ (i j : ι) (hij : i ≤ j) (x : G 
i), (g j) (f i j hij x) = (g i) x) (i : ι) (x : G i),   (Ring.DirectLimit.lift G
 f P g Hg) ((Ring.DirectLimit.of G f i) x) = (g i) x
参数：i : ι；G i；i j : ι；P : Type u_3；g : (i : ι) → G i →+* P；Hg : ∀ (i j : ι) (hij 
: i ≤ j) (x : G i), (g j) (f i j hij x) = (g i) x；i : ι；x : G i；Ring.DirectLimit
.lift G f P g Hg；(Ring.DirectLimit.of G f i) x；g i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeCommRing.lift_of`：lift_of (x : α) : lift f (of x) = f x
-/
@[simp] theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x :=
  FreeCommRing.lift_of _ _

@[ext]
/-
**Ring.DirectLimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：hom_ext {g₁ g₂ : DirectLimit G f ->+* P} (h : forall i, g₁.comp (of G f i)
 = g₂.comp (of G f i)) : g₁ = g₂
参数：h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `FreeCommRing.hom_ext`：hom_ext ⦃f g : FreeCommRing α ->+* R⦄ (h : forall 
x, f (of x) = g (of x)) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f →+* P} (h : ∀ i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ :=
  Ideal.Quotient.ringHom_ext <| FreeCommRing.hom_ext fun ⟨i, x⟩ => congr($(h i) x)

@[simp]
/-
**Ring.DirectLimit.lift_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：lift_comp_of (F : DirectLimit G f ->+* P) : lift G f _ (fun i => F.comp <|
 of G f i) (fun i j hij x => by simp) = F
参数：F : DirectLimit G f ->+* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.DirectLimit.hom_ext`：hom_ext {g₁ g₂ : DirectLimit G f ->+* P} (h : 
forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) : g₁ = g₂
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.DirectLimit.lift_of`：∀ {ι : Type u_1} [inst : Preorder ι] {G : ι → 
Type u_2} [inst_1 : (i : ι) → CommRing (G i)]   {f : (i j : ι) → i ≤ j → G i → G
 j} (P : Type …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_comp_of (F : DirectLimit G f →+* P) :
    lift G f _ (fun i ↦ F.comp <| of G f i) (fun i j hij x ↦ by simp) = F := by
  ext; simp

@[simp]
/-
**Ring.DirectLimit.lift_of'** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：lift_of' : lift G f _ (of G f) (fun i j hij x => by simp) = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.DirectLimit.hom_ext`：hom_ext {g₁ g₂ : DirectLimit G f ->+* P} (h : 
forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) : g₁ = g₂
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.DirectLimit.lift_of`：∀ {ι : Type u_1} [inst : Preorder ι] {G : ι → 
Type u_2} [inst_1 : (i : ι) → CommRing (G i)]   {f : (i j : ι) → i ≤ j → G i → G
 j} (P : Type …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_of' : lift G f _ (of G f) (fun i j hij x ↦ by simp) = .id _ := by
  ext; simp
/-
**Ring.DirectLimit.lift_injective** 是 Mathlib 中的一个引理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：lift_injective [Nonempty ι] [IsDirectedOrder ι] (injective : forall i, Fun
ction.Injective <| g i) : Function.Injective (lift G f P g Hg)
参数：injective : forall i, Function.Injective <| g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Ring.DirectLimit.induction_on`：induction_on [Nonempty ι] [IsDirectedOrde
r ι] {C : DirectLimit G f -> Prop} (z : DirectLimit G f) (ih : forall i x, C (of
 G f i x)) : C z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ring.DirectLimit.lift_of`：∀ {ι : Type u_1} [inst : Preorder ι] {G : ι → 
Type u_2} [inst_1 : (i : ι) → CommRing (G i)]   {f : (i j : ι) → i ≤ j → G i → G
 j} (P : Type …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma lift_injective [Nonempty ι] [IsDirectedOrder ι]
    (injective : ∀ i, Function.Injective <| g i) :
    Function.Injective (lift G f P g Hg) := by
  simp_rw [injective_iff_map_eq_zero] at injective ⊢
  intro z hz
  induction z using DirectLimit.induction_on with
  | ih _ g => rw [lift_of] at hz; rw [injective _ g hz, map_zero]

section OfZeroExact

variable (f' : ∀ i j, i ≤ j → G i →+* G j)
variable [DirectedSystem G fun i j h ↦ f' i j h] [IsDirectedOrder ι]
variable (G f)

open _root_.DirectLimit in
/-- The direct limit constructed as a quotient of the free commutative ring is isomorphic to
the direct limit constructed as a quotient of the disjoint union. -/
/-
**Ring.DirectLimit.ringEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ring.DirectLimit`。
形式化陈述：ringEquiv [Nonempty ι] : DirectLimit G (f' · · ·) ≃+* _root_.DirectLimit G
 f'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direct limit constructed as a quotient of the free commutative ring is isomo
rphic to
the direct limit constructed as a quotient of the disjoint union.
-/
def ringEquiv [Nonempty ι] : DirectLimit G (f' · · ·) ≃+* _root_.DirectLimit G f' :=
  .ofRingHom (lift _ _ _ (Ring.of _ _) fun _ _ _ _ ↦ .symm <| eq_of_le ..)
    (Ring.lift _ _ _ (of _ _) fun _ _ _ _ ↦ of_f ..)
    (by ext; simp)
    (by ext; simp)

@[simp]
/-
**Ring.DirectLimit.ringEquiv_of** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：ringEquiv_of [Nonempty ι] {i g} : ringEquiv G f' (of _ _ i g) = ⟦⟨i, g⟩⟧
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.ofRingHom_apply`：∀ {R : Type u_4} {S : Type u_5} [inst : NonAs
socSemiring R] [inst_1 : NonAssocSemiring S] (f : R →+* S) (g : S →+* R)   (h₁ :
 f.comp g = Rin…
· 使用定理 `Ring.DirectLimit.lift_of`：∀ {ι : Type u_1} [inst : Preorder ι] {G : ι → 
Type u_2} [inst_1 : (i : ι) → CommRing (G i)]   {f : (i j : ι) → i ≤ j → G i → G
 j} (P : Type …
· 使用定理 `DirectLimit.Ring.of_apply`：∀ {ι : Type u_2} [inst : Preorder ι] (G : ι →
 Type u_3) {T : ⦃i j : ι⦄ → i ≤ j → Type u_6}   (f : (x x_1 : ι) → (h : x ≤ x_1)
 → T h) [inst_1…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ringEquiv_of [Nonempty ι] {i g} : ringEquiv G f' (of _ _ i g) = ⟦⟨i, g⟩⟧ := by
  simp [ringEquiv]

@[simp]
/-
**Ring.DirectLimit.ringEquiv_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit
`。
形式化陈述：ringEquiv_symm_mk [Nonempty ι] {g} : (ringEquiv G f').symm ⟦g⟧ = of _ _ g.
1 g.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem ringEquiv_symm_mk [Nonempty ι] {g} : (ringEquiv G f').symm ⟦g⟧ = of _ _ g.1 g.2 := rfl

variable {G f'}
/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
/-
**Ring.DirectLimit.of.zero_exact** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit.of`
。
形式化陈述：∀ {ι : Type u_1} [inst : Preorder ι] {G : ι → Type u_2} [inst_1 : (i : ι) 
→ CommRing (G i)]   {f' : (i j : ι) → i ≤ j → G i →+* G j} [DirectedSystem G fun
 i j h => ⇑(f' i j h)] [IsDirectedOrder ι] {i : ι}   {x : G i}, (Ring.DirectLimi
t.of G (fun x1 x2 x3 => ⇑(f' x1 x2 x3)) i) x = 0 → ∃ j, ∃ (hij : i ≤ j), (f' i j
 hij) x = 0
参数：i : ι；G i；i j : ι；f' i j h；Ring.DirectLimit.of G (fun x1 x2 x3 => ⇑(f' x1 x2 
x3)) i；hij : i ≤ j；f' i j hij。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectLimit.exists_eq_zero`：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι 
→ Type u_3} {T : ⦃i j : ι⦄ → i ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1
) → T h} [inst_1…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Ring.DirectLimit.ringEquiv_of`：ringEquiv_of [Nonempty ι] {i g} : ringEqu
iv G f' (of _ _ i g) = ⟦⟨i, g⟩⟧
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system.
-/
theorem of.zero_exact {i x} (hix : of G (f' · · ·) i x = 0) :
    ∃ (j : _) (hij : i ≤ j), f' i j hij x = 0 := by
  have := Nonempty.intro i
  apply_fun ringEquiv _ _ at hix
  rwa [map_zero, ringEquiv_of, DirectLimit.exists_eq_zero] at hix

end OfZeroExact

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

/-- If the maps in the directed system are injective, then the canonical maps
from the components to the direct limits are injective. -/
/-
**Ring.DirectLimit.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：of_injective [IsDirectedOrder ι] [DirectedSystem G fun i j h => f' i j h] 
(hf : forall i j hij, Function.Injective (f' i j hij)) (i) : Function.Injective 
(of G (fun i j h => f' i j h) i)
参数：hf : forall i j hij, Function.Injective (f' i j hij)；i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Equiv.comp_injective`：comp_injective (f : α -> β) (e : β ≃ γ) : Injectiv
e (e ∘ f) ↔ Injective f
· 使用定理 `DirectLimit.mk_injective`：mk_injective (h : forall i j hij, Function.Inj
ective (f i j hij)) (i) : Function.Injective fun x => (⟦⟨i, x⟩⟧ : DirectLimit F 
f)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If the maps in the directed system are injective, then the canonical maps
from the components to the direct limits are injective.
-/
theorem of_injective [IsDirectedOrder ι] [DirectedSystem G fun i j h ↦ f' i j h]
    (hf : ∀ i j hij, Function.Injective (f' i j hij)) (i) :
    Function.Injective (of G (fun i j h ↦ f' i j h) i) :=
  have := Nonempty.intro i
  ((ringEquiv _ _).comp_injective _).mp
    fun _ _ eq ↦ DirectLimit.mk_injective f' hf _ (by simpa only [← ringEquiv_of])

section functorial

variable {f : ∀ i j, i ≤ j → G i →+* G j}
variable {G' : ι → Type*} [∀ i, CommRing (G' i)]
variable {f' : ∀ i j, i ≤ j → G' i →+* G' j}
variable {G'' : ι → Type*} [∀ i, CommRing (G'' i)]
variable {f'' : ∀ i j, i ≤ j → G'' i →+* G'' j}

/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of ring homomorphisms `gᵢ : Gᵢ ⟶ G'ᵢ` such that `g ∘ f = f' ∘ g` induces a ring
homomorphism `lim G ⟶ lim G'`.
-/
/-
**Ring.DirectLimit.map** 是 Mathlib 中的一个定义，位于命名空间 `Ring.DirectLimit`。
形式化陈述：map (g : (i : ι) -> G i ->+* G' i) (hg : forall i j h, (g j).comp (f i j h
) = (f' i j h).comp (g i)) : DirectLimit G (fun _ _ h => f _ _ h) ->+* DirectLim
it G' fun _ _ h => f' _ _ h
参数：g : (i : ι) -> G i ->+* G' i；hg : forall i j h, (g j).comp (f i j h) = (f' i 
j h).comp (g i)。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` resp
ectively, any
family of ring homomorphisms `gᵢ : Gᵢ ⟶ G'ᵢ` such that `g ∘ f = f' ∘ g` induces 
a ring
homomorphism `lim G ⟶ lim G'`.
-/
def map (g : (i : ι) → G i →+* G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i)) :
    DirectLimit G (fun _ _ h ↦ f _ _ h) →+* DirectLimit G' fun _ _ h ↦ f' _ _ h :=
  lift _ _ _ (fun i ↦ (of _ _ _).comp (g i)) fun i j h g ↦ by
      have eq1 := DFunLike.congr_fun (hg i j h) g
      simp only [RingHom.coe_comp, Function.comp_apply] at eq1 ⊢
      rw [eq1, of_f]
/-
**Ring.DirectLimit.map_apply_of** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：∀ {ι : Type u_1} [inst : Preorder ι] {G : ι → Type u_2} [inst_1 : (i : ι) 
→ CommRing (G i)]   {f : (i j : ι) → i ≤ j → G i →+* G j} {G' : ι → Type u_4} [i
nst_2 : (i : ι) → CommRing (G' i)]   {f' : (i j : ι) → i ≤ j → G' i →+* G' j} (g
 : (i : ι) → G i →+* G' i)   (hg : ∀ (i j : ι) (h : i ≤ j), (g j).comp (f i j h)
 = (f' i j h).comp (g i)) {i : ι} (x : G i),   (Ring.DirectLimit.map g hg) ((Rin
g.DirectLimit.of G (fun x x_1 h => ⇑(f x x_1 h)) i) x) =     (Ring.DirectLimit.o
f G' (fun x x_1 h => ⇑(f' x x_1 h)) i) ((g i) x)
参数：i : ι；G i；i j : ι；i : ι；G' i；i j : ι；g : (i : ι) → G i →+* G' i；hg : ∀ (i j :
 ι) (h : i ≤ j), (g j).comp (f i j h) = (f' i j h).comp (g i)；x : G i；Ring.Direc
tLimit.map g hg；(Ring.DirectLimit.of G (fun x x_1 h => ⇑(f x x_1 h)) i) x；Ring.D
irectLimit.of G' (fun x x_1 h => ⇑(f' x x_1 h)) i；(g i) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.DirectLimit.lift_of`：∀ {ι : Type u_1} [inst : Preorder ι] {G : ι → 
Type u_2} [inst_1 : (i : ι) → CommRing (G i)]   {f : (i j : ι) → i ≤ j → G i → G
 j} (P : Type …
-/
@[simp] lemma map_apply_of (g : (i : ι) → G i →+* G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i))
    {i : ι} (x : G i) :
    map g hg (of G _ _ x) = of G' (fun _ _ h ↦ f' _ _ h) i (g i x) :=
  lift_of _ _ _ _ _
/-
**Ring.DirectLimit.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：∀ {ι : Type u_1} [inst : Preorder ι] {G : ι → Type u_2} [inst_1 : (i : ι) 
→ CommRing (G i)]   {f : (i j : ι) → i ≤ j → G i →+* G j},   Ring.DirectLimit.ma
p (fun x => RingHom.id (G x)) ⋯ = RingHom.id (Ring.DirectLimit G fun x x_1 h => 
⇑(f x x_1 h))
参数：i : ι；G i；i j : ι；fun x => RingHom.id (G x)；Ring.DirectLimit G fun x x_1 h =>
 ⇑(f x x_1 h)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.DirectLimit.hom_ext`：hom_ext {g₁ g₂ : DirectLimit G f ->+* P} (h : 
forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) : g₁ = g₂
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.DirectLimit.map_apply_of`：∀ {ι : Type u_1} [inst : Preorder ι] {G :
 ι → Type u_2} [inst_1 : (i : ι) → CommRing (G i)]   {f : (i j : ι) → i ≤ j → G 
i →+* G j} {G' : ι …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_id :
    map (fun _ ↦ RingHom.id _) (fun _ _ _ ↦ rfl) = .id (DirectLimit G fun _ _ h ↦ f _ _ h) := by
  ext; simp
/-
**Ring.DirectLimit.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：map_comp (g₁ : (i : ι) -> G i ->+* G' i) (g₂ : (i : ι) -> G' i ->+* G'' i)
 (hg₁ : forall i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i)) (hg₂ : for
all i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) : ((map g₂ hg₂).com
p (map g₁ hg₁) : DirectLimit G (fun _ _ h => f _ _ h) ->+* DirectLimit G'' fun _
 _ h => f'' _ _ h) = (map (fun i => (g₂ i).comp (g₁ i)) fun i j h => by rw [Ring
Hom.comp_assoc]; rw [hg₁ i]; rw [← RingHom.comp_assoc]; rw [hg₂ i]; rw [RingHom.
comp_assoc] : DirectLimit 
参数：g₁ : (i : ι) -> G i ->+* G' i；g₂ : (i : ι) -> G' i ->+* G'' i；hg₁ : forall i 
j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i)；hg₂ : forall i j h, (g₂ j).c
omp (f' i j h) = (f'' i j h).comp (g₂ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.DirectLimit.hom_ext`：hom_ext {g₁ g₂ : DirectLimit G f ->+* P} (h : 
forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) : g₁ = g₂
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.DirectLimit.map_apply_of`：∀ {ι : Type u_1} [inst : Preorder ι] {G :
 ι → Type u_2} [inst_1 : (i : ι) → CommRing (G i)]   {f : (i j : ι) → i ≤ j → G 
i →+* G j} {G' : ι …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp (g₁ : (i : ι) → G i →+* G' i) (g₂ : (i : ι) → G' i →+* G'' i)
    (hg₁ : ∀ i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i))
    (hg₂ : ∀ i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) :
    ((map g₂ hg₂).comp (map g₁ hg₁) :
      DirectLimit G (fun _ _ h ↦ f _ _ h) →+* DirectLimit G'' fun _ _ h ↦ f'' _ _ h) =
    (map (fun i ↦ (g₂ i).comp (g₁ i)) fun i j h ↦ by
      rw [RingHom.comp_assoc, hg₁ i, ← RingHom.comp_assoc, hg₂ i, RingHom.comp_assoc] :
      DirectLimit G (fun _ _ h ↦ f _ _ h) →+* DirectLimit G'' fun _ _ h ↦ f'' _ _ h) := by
  ext; simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equivalence
`lim G ⟶ lim G'`.
-/
/-
**Ring.DirectLimit.congr** 是 Mathlib 中的一个定义，位于命名空间 `Ring.DirectLimit`。
形式化陈述：congr (e : (i : ι) -> G i ≃+* G' i) (he : forall i j h, (e j).toRingHom.co
mp (f i j h) = (f' i j h).comp (e i)) : DirectLimit G (fun _ _ h => f _ _ h) ≃+*
 DirectLimit G' fun _ _ h => f' _ _ h
参数：e : (i : ι) -> G i ≃+* G' i；he : forall i j h, (e j).toRingHom.comp (f i j h)
 = (f' i j h).comp (e i)。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` resp
ectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equ
ivalence
`lim G ⟶ lim G'`.
-/
def congr (e : (i : ι) → G i ≃+* G' i)
    (he : ∀ i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i)) :
    DirectLimit G (fun _ _ h ↦ f _ _ h) ≃+* DirectLimit G' fun _ _ h ↦ f' _ _ h :=
  RingEquiv.ofRingHom
    (map (e ·) he)
    (map (fun i ↦ (e i).symm) fun i j h ↦ DFunLike.ext _ _ fun x ↦ by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        RingEquiv.apply_symm_apply] at eq1 ⊢
      simp [← eq1])
    (by simp [map_comp]) (by simp [map_comp])
/-
**Ring.DirectLimit.congr_apply_of** 是 Mathlib 中的一个引理，位于命名空间 `Ring.DirectLimit`。
形式化陈述：congr_apply_of (e : (i : ι) -> G i ≃+* G' i) (he : forall i j h, (e j).toR
ingHom.comp (f i j h) = (f' i j h).comp (e i)) {i : ι} (g : G i) : congr e he (o
f G _ i g) = of G' (fun _ _ h => f' _ _ h) i (e i g)
参数：e : (i : ι) -> G i ≃+* G' i；he : forall i j h, (e j).toRingHom.comp (f i j h)
 = (f' i j h).comp (e i)；g : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Ring.DirectLimit.map_apply_of`：∀ {ι : Type u_1} [inst : Preorder ι] {G :
 ι → Type u_2} [inst_1 : (i : ι) → CommRing (G i)]   {f : (i j : ι) → i ≤ j → G 
i →+* G j} {G' : ι …
-/
lemma congr_apply_of (e : (i : ι) → G i ≃+* G' i)
    (he : ∀ i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G i) :
    congr e he (of G _ i g) = of G' (fun _ _ h ↦ f' _ _ h) i (e i g) :=
  map_apply_of _ he _

set_option backward.isDefEq.respectTransparency.types false in
/-
**Ring.DirectLimit.congr_symm_apply_of** 是 Mathlib 中的一个引理，位于命名空间 `Ring.DirectLim
it`。
形式化陈述：congr_symm_apply_of (e : (i : ι) -> G i ≃+* G' i) (he : forall i j h, (e j
).toRingHom.comp (f i j h) = (f' i j h).comp (e i)) {i : ι} (g : G' i) : (congr 
e he).symm (of G' _ i g) = of G (fun _ _ h => f _ _ h) i ((e i).symm g)
参数：e : (i : ι) -> G i ≃+* G' i；he : forall i j h, (e j).toRingHom.comp (f i j h)
 = (f' i j h).comp (e i)；g : G' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.ofRingHom_symm_apply`：∀ {R : Type u_4} {S : Type u_5} [inst : 
NonAssocSemiring R] [inst_1 : NonAssocSemiring S] (f : R →+* S) (g : S →+* R)   
(h₁ : f.comp g = Rin…
· 使用定理 `Ring.DirectLimit.map_apply_of`：∀ {ι : Type u_1} [inst : Preorder ι] {G :
 ι → Type u_2} [inst_1 : (i : ι) → CommRing (G i)]   {f : (i j : ι) → i ≤ j → G 
i →+* G j} {G' : ι …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma congr_symm_apply_of (e : (i : ι) → G i ≃+* G' i)
    (he : ∀ i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G' i) :
    (congr e he).symm (of G' _ i g) = of G (fun _ _ h ↦ f _ _ h) i ((e i).symm g) := by
  simp only [congr, RingEquiv.ofRingHom_symm_apply, map_apply_of, RingHom.coe_coe]

end functorial

end DirectLimit

end

end Ring

namespace Field

variable [Nonempty ι] [IsDirectedOrder ι] [∀ i, Field (G i)]
variable (f : ∀ i j, i ≤ j → G i → G j)
variable (f' : ∀ i j, i ≤ j → G i →+* G j)

namespace DirectLimit

/-
**Field.DirectLimit.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Field.DirectLimit`。
形式化陈述：nontrivial [DirectedSystem G (f' · · ·)] : Nontrivial (Ring.DirectLimit G 
(f' · · ·))
参数：f' · · ·。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `Ring.DirectLimit.of.zero_exact`：∀ {ι : Type u_1} [inst : Preorder ι] {G 
: ι → Type u_2} [inst_1 : (i : ι) → CommRing (G i)]   {f' : (i j : ι) → i ≤ j → 
G i →+* G j} [Direct…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
instance nontrivial [DirectedSystem G (f' · · ·)] :
    Nontrivial (Ring.DirectLimit G (f' · · ·)) :=
  ⟨⟨0, 1,
      Nonempty.elim (by infer_instance) fun i : ι ↦ by
        change (0 : Ring.DirectLimit G (f' · · ·)) ≠ 1
        rw [← (Ring.DirectLimit.of _ _ _).map_one]
        · intro H; rcases Ring.DirectLimit.of.zero_exact H.symm with ⟨j, hij, hf⟩
          rw [(f' i j hij).map_one] at hf
          exact one_ne_zero hf⟩⟩
/-
**Field.DirectLimit.exists_inv** 是 Mathlib 中的一个定理，位于命名空间 `Field.DirectLimit`。
形式化陈述：exists_inv {p : Ring.DirectLimit G f} : p != 0 -> exists y, p * y = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.DirectLimit.induction_on`：induction_on [Nonempty ι] [IsDirectedOrde
r ι] {C : DirectLimit G f -> Prop} (z : DirectLimit G f) (ih : forall i x, C (of
 G f i x)) : C z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
-/
theorem exists_inv {p : Ring.DirectLimit G f} : p ≠ 0 → ∃ y, p * y = 1 :=
  Ring.DirectLimit.induction_on p fun i x H ↦
    ⟨Ring.DirectLimit.of G f i x⁻¹, by
      rw [← (Ring.DirectLimit.of _ _ _).map_mul,
        mul_inv_cancel₀ fun h : x = 0 ↦ H <| by rw [h, (Ring.DirectLimit.of _ _ _).map_zero],
        (Ring.DirectLimit.of _ _ _).map_one]⟩

section


open scoped Classical in
/-- Noncomputable multiplicative inverse in a direct limit of fields. -/
/-
**Field.DirectLimit.inv** 是 Mathlib 中的一个定义，位于命名空间 `Field.DirectLimit`。
形式化陈述：inv (p : Ring.DirectLimit G f) : Ring.DirectLimit G f
参数：p : Ring.DirectLimit G f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Field.DirectLimit.exists_inv`：exists_inv {p : Ring.DirectLimit G f} : p 
!= 0 -> exists y, p * y = 1

--- 原说明 ---
Noncomputable multiplicative inverse in a direct limit of fields.
-/
noncomputable def inv (p : Ring.DirectLimit G f) : Ring.DirectLimit G f :=
  if H : p = 0 then 0 else Classical.choose (DirectLimit.exists_inv G f H)
/-
**Field.DirectLimit.mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Field.DirectLimit`
。
形式化陈述：∀ {ι : Type u_1} [inst : Preorder ι] (G : ι → Type u_2) [inst_1 : Nonempty
 ι] [inst_2 : IsDirectedOrder ι]   [inst_3 : (i : ι) → Field (G i)] (f : (i j : 
ι) → i ≤ j → G i → G j) {p : Ring.DirectLimit G f},   p ≠ 0 → p * Field.DirectLi
mit.inv G f p = 1
参数：G : ι → Type u_2；i : ι；G i；f : (i j : ι) → i ≤ j → G i → G j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.DirectLimit.exists_inv`：exists_inv {p : Ring.DirectLimit G f} : p 
!= 0 -> exists y, p * y = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.DirectLimit.inv.eq_1`：∀ {ι : Type u_1} [inst : Preorder ι] (G : ι 
→ Type u_2) [inst_1 : Nonempty ι] [inst_2 : IsDirectedOrder ι]   [inst_3 : (i : 
ι) → Field (G i)…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
protected theorem mul_inv_cancel {p : Ring.DirectLimit G f} (hp : p ≠ 0) : p * inv G f p = 1 := by
  rw [inv, dif_neg hp, Classical.choose_spec (DirectLimit.exists_inv G f hp)]
/-
**Field.DirectLimit.inv_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Field.DirectLimit`
。
形式化陈述：∀ {ι : Type u_1} [inst : Preorder ι] (G : ι → Type u_2) [inst_1 : Nonempty
 ι] [inst_2 : IsDirectedOrder ι]   [inst_3 : (i : ι) → Field (G i)] (f : (i j : 
ι) → i ≤ j → G i → G j) {p : Ring.DirectLimit G f},   p ≠ 0 → Field.DirectLimit.
inv G f p * p = 1
参数：G : ι → Type u_2；i : ι；G i；f : (i j : ι) → i ≤ j → G i → G j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Field.DirectLimit.mul_inv_cancel`：∀ {ι : Type u_1} [inst : Preorder ι] (
G : ι → Type u_2) [inst_1 : Nonempty ι] [inst_2 : IsDirectedOrder ι]   [inst_3 :
 (i : ι) → Field (G i)…
-/
protected theorem inv_mul_cancel {p : Ring.DirectLimit G f} (hp : p ≠ 0) : inv G f p * p = 1 := by
  rw [_root_.mul_comm, DirectLimit.mul_inv_cancel G f hp]

/-- Noncomputable field structure on the direct limit of fields.
See note [reducible non-instances]. -/
/-
**Field.DirectLimit.field** 是 Mathlib 中的一个定义，位于命名空间 `Field.DirectLimit`。
形式化陈述：{ι : Type u_1} →   [inst : Preorder ι] →     (G : ι → Type u_2) →       [N
onempty ι] →         [IsDirectedOrder ι] →           [inst_3 : (i : ι) → Field (
G i)] →             (f' : (i j : ι) → i ≤ j → G i →+* G j) →               [Dire
ctedSystem G fun x1 x2 x3 => ⇑(f' x1 x2 x3)] →                 Field (Ring.Direc
tLimit G fun x1 x2 x3 => ⇑(f' x1 x2 x3))
参数：G : ι → Type u_2；i : ι；G i；f' : (i j : ι) → i ≤ j → G i →+* G j；f' x1 x2 x3；R
ing.DirectLimit G fun x1 x2 x3 => ⇑(f' x1 x2 x3)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noncomputable field structure on the direct limit of fields.
See note [reducible non-instances].
-/
protected noncomputable abbrev field [DirectedSystem G (f' · · ·)] :
    Field (Ring.DirectLimit G (f' · · ·)) where
  -- This used to include the parent CommRing and Nontrivial instances,
  -- but leaving them implicit avoids a very expensive (2-3 minutes!) eta expansion.
  inv := inv G (f' · · ·)
  mul_inv_cancel := fun _ ↦ DirectLimit.mul_inv_cancel G (f' · · ·)
  inv_zero := dif_pos rfl
  nnqsmul := _
  nnqsmul_def _ _ := rfl
  qsmul := _
  qsmul_def _ _ := rfl

end

end DirectLimit

end Field

