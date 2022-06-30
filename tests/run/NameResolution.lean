import Aesop

set_option aesop.check.all true

-- When parsing the names of declarations for local rules, Aesop should take the
-- currently opened namespaces into account.

example : List α := by
  aesop (add safe List.nil)

namespace List

example : List α := by
  aesop (add safe List.nil)

example : List α := by
  aesop (add safe nil)

end List
