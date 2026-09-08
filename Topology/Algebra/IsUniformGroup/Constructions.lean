/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Constructions of new uniform groups from old ones
-/

public section

variable {G H hom : Type*} [Group G] [Group H]

section LatticeOps

@[to_additive]
/-
**isUniformGroup_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformGroup_sInf {us : Set (UniformSpace G)} (h : forall u in us, @IsUn
iformGroup G u _) : @IsUniformGroup G (sInf us) _
参数：UniformSpace G；h : forall u in us, @IsUniformGroup G u _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `uniformContinuous_sInf_rng`：uniformContinuous_sInf_rng {f : α -> β} {u₁ 
: UniformSpace α} {u₂ : Set (UniformSpace β)} : UniformContinuous[u₁, sInf u₂] f
 ↔ forall u in u…
· 使用定理 `uniformContinuous_sInf_dom₂`：uniformContinuous_sInf_dom₂ {α β γ} {f : α 
-> β -> γ} {uas : Set (UniformSpace α)} {ubs : Set (UniformSpace β)} {ua : Unifo
rmSpace α} {ub : …
· 使用定理 `IsUniformGroup.uniformContinuous_div`：∀ {α : Type u_3} {inst : UniformSp
ace α} {inst_1 : Group α} [self : IsUniformGroup α],   UniformContinuous fun p =
> p.1 / p.2
-/
theorem isUniformGroup_sInf {us : Set (UniformSpace G)} (h : ∀ u ∈ us, @IsUniformGroup G u _) :
    @IsUniformGroup G (sInf us) _ :=
  @IsUniformGroup.mk G (_) _ <|
    uniformContinuous_sInf_rng.mpr fun u hu =>
      uniformContinuous_sInf_dom₂ hu hu (@IsUniformGroup.uniformContinuous_div G u _ (h u hu))

@[to_additive]
/-
**isUniformGroup_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformGroup_iInf {ι : Sort*} {us' : ι -> UniformSpace G} (h' : forall i
, @IsUniformGroup G (us' i) _) : @IsUniformGroup G (⨅ i, us' i) _
参数：h' : forall i, @IsUniformGroup G (us' i) _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用定理 `isUniformGroup_sInf`：isUniformGroup_sInf {us : Set (UniformSpace G)} (h 
: forall u in us, @IsUniformGroup G u _) : @IsUniformGroup G (sInf us) _
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem isUniformGroup_iInf {ι : Sort*} {us' : ι → UniformSpace G}
    (h' : ∀ i, @IsUniformGroup G (us' i) _) : @IsUniformGroup G (⨅ i, us' i) _ := by
  rw [← sInf_range]
  exact isUniformGroup_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
/-
**isUniformGroup_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUniformGroup_inf {u₁ u₂ : UniformSpace G} (h₁ : @IsUniformGroup G u₁ _) 
(h₂ : @IsUniformGroup G u₂ _) : @IsUniformGroup G (u₁ ⊓ u₂) _
参数：h₁ : @IsUniformGroup G u₁ _；h₂ : @IsUniformGroup G u₂ _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] (x y : α), x ⊓ 
y = ⨅ b, bif b then x else y
· 使用定理 `isUniformGroup_iInf`：isUniformGroup_iInf {ι : Sort*} {us' : ι -> Uniform
Space G} (h' : forall i, @IsUniformGroup G (us' i) _) : @IsUniformGroup G (⨅ i, 
us' i) _
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isUniformGroup_inf {u₁ u₂ : UniformSpace G} (h₁ : @IsUniformGroup G u₁ _)
    (h₂ : @IsUniformGroup G u₂ _) : @IsUniformGroup G (u₁ ⊓ u₂) _ := by
  rw [inf_eq_iInf]
  refine isUniformGroup_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

section Comap

@[to_additive]
/-
**IsUniformInducing.isUniformGroup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUniformInducing.isUniformGroup [UniformSpace G] [UniformSpace H] [IsUnif
ormGroup H] [FunLike hom G H] [MonoidHomClass hom G H] (f : hom) (hf : IsUniform
Inducing f) : IsUniformGroup G where uniformContinuous_div
参数：f : hom；hf : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous_iff`：IsUniformInducing.uniformContin
uous_iff {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g) : UniformContinuou
s f ↔ UniformContinuous (g ∘ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `uniformContinuous_div`：uniformContinuous_div : UniformContinuous fun p :
 α × α => p.1 / p.2
· 使用定理 `UniformContinuous.prodMap`：UniformContinuous.prodMap [UniformSpace δ] {f
 : α -> γ} {g : β -> δ} (hf : UniformContinuous f) (hg : UniformContinuous g) : 
UniformContinuo…
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
-/
lemma IsUniformInducing.isUniformGroup [UniformSpace G] [UniformSpace H]
    [IsUniformGroup H] [FunLike hom G H] [MonoidHomClass hom G H]
    (f : hom) (hf : IsUniformInducing f) :
    IsUniformGroup G where
  uniformContinuous_div := by
    simp_rw [hf.uniformContinuous_iff, Function.comp_def, map_div]
    exact uniformContinuous_div.comp (hf.uniformContinuous.prodMap hf.uniformContinuous)

@[to_additive]
/-
**IsUniformGroup.comap** 是 Mathlib 中的一个定理，位于命名空间 `IsUniformGroup`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} {hom : Type u_3} [inst : Group G] [inst_1 
: Group H] {u : UniformSpace H}   [IsUniformGroup H] [inst_3 : FunLike hom G H] 
[MonoidHomClass hom G H] (f : hom), IsUniformGroup G
参数：f : hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUniformInducing.isUniformGroup`：IsUniformInducing.isUniformGroup [Unif
ormSpace G] [UniformSpace H] [IsUniformGroup H] [FunLike hom G H] [MonoidHomClas
s hom G H] (f : hom) (…
-/
protected theorem IsUniformGroup.comap {u : UniformSpace H} [IsUniformGroup H]
    [FunLike hom G H] [MonoidHomClass hom G H] (f : hom) :
    @IsUniformGroup G (u.comap f) _ :=
  letI : UniformSpace G := u.comap f; IsUniformInducing.isUniformGroup f ⟨rfl⟩

end Comap

section PiProd

@[to_additive]
/-
**Prod.instIsUniformGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instIsUniformGroup [UniformSpace G] [hG : IsUniformGroup G] [UniformS
pace H] [hH : IsUniformGroup H] : IsUniformGroup (G × H)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instUniformSpaceProd.eq_1`：∀ {α : Type ua} {β : Type ub} [u₁ : UniformSp
ace α] [u₂ : UniformSpace β],   instUniformSpaceProd = UniformSpace.comap Prod.f
st u₁ ⊓ Uniform…
· 使用定理 `isUniformGroup_inf`：isUniformGroup_inf {u₁ u₂ : UniformSpace G} (h₁ : @I
sUniformGroup G u₁ _) (h₂ : @IsUniformGroup G u₂ _) : @IsUniformGroup G (u₁ ⊓ u₂
) _
· 使用定理 `IsUniformGroup.comap`：∀ {G : Type u_1} {H : Type u_2} {hom : Type u_3} [
inst : Group G] [inst_1 : Group H] {u : UniformSpace H}   [IsUniformGroup H] [in
st_3 : Fun…
-/
instance Prod.instIsUniformGroup [UniformSpace G] [hG : IsUniformGroup G]
    [UniformSpace H] [hH : IsUniformGroup H] :
    IsUniformGroup (G × H) := by
  rw [instUniformSpaceProd]
  exact isUniformGroup_inf (.comap <| MonoidHom.fst G H) (.comap <| MonoidHom.snd G H)

@[to_additive]
/-
**Pi.instIsUniformGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instIsUniformGroup {ι : Type*} {G : ι -> Type*} [forall i, UniformSpace
 (G i)] [forall i, Group (G i)] [forall i, IsUniformGroup (G i)] : IsUniformGrou
p (forall i, G i)
参数：G i；G i；G i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.uniformSpace_eq`：Pi.uniformSpace_eq : Pi.uniformSpace α = ⨅ i, Unifor
mSpace.comap (eval i) (U i)
· 使用定理 `isUniformGroup_iInf`：isUniformGroup_iInf {ι : Sort*} {us' : ι -> Uniform
Space G} (h' : forall i, @IsUniformGroup G (us' i) _) : @IsUniformGroup G (⨅ i, 
us' i) _
· 使用定理 `IsUniformGroup.comap`：∀ {G : Type u_1} {H : Type u_2} {hom : Type u_3} [
inst : Group G] [inst_1 : Group H] {u : UniformSpace H}   [IsUniformGroup H] [in
st_3 : Fun…
-/
instance Pi.instIsUniformGroup {ι : Type*} {G : ι → Type*} [∀ i, UniformSpace (G i)]
    [∀ i, Group (G i)] [∀ i, IsUniformGroup (G i)] : IsUniformGroup (∀ i, G i) := by
  rw [Pi.uniformSpace_eq]
  exact isUniformGroup_iInf fun i ↦ .comap (Pi.evalMonoidHom G i)

end PiProd

section DiscreteUniformity

/-- The discrete uniformity makes a group a `IsUniformGroup`. -/
@[to_additive /-- The discrete uniformity makes an additive group a `IsUniformAddGroup`. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete uniformity makes a group a `IsUniformGroup`.
-/
instance [UniformSpace G] [DiscreteUniformity G] : IsUniformGroup G where
  uniformContinuous_div := DiscreteUniformity.uniformContinuous (G × G) fun p ↦ p.1 / p.2

end DiscreteUniformity

