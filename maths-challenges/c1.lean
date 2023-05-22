def injective {X Y : Type} (f : X → Y) : Prop := ∀ (a b : X), f a = f b → a = b

theorem challenge1 {X Y Z : Type}
  (f : X → Y) (hf : injective f)
  (g : Y → Z) (hg : injective g)
: injective (g ∘ f) := by
  intro a b hgf
  apply hf
  apply hg
  exact hgf
