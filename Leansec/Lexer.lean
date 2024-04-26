import Lean.Data.Trie
import Leansec.Span

namespace Leansec.Lexer

-- TODO: check out how [logos](https://github.com/maciejhirsz/logos) works
-- And this also should be separate library

-- structure LexParameters where
--   Tok : Type _
--   -- TODO: Replace with hashmap like typeclass
--   keywords : List (String × Tok)
--   isBreaking :
