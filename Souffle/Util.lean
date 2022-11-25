namespace Souffle

/-
Native joinSep for arrays
-/
protected def joinSep {α : Type u} [ToString α] (items: Array α)  (pre: String := "") (sep: String := ", ") (post: String := ""): String :=
  (if items.size > 0 then pre else "")
    ++ items.foldl (init := "") (fun acc item => acc ++ if acc.length == 0 then (toString item) else sep ++ (toString item))
    ++ post

/-
Escape values that may contain new lines
-/
protected def escape (str: String) : String := str.replace "\n" "\\n"
