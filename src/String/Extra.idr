-- --------------------------------------------------------------- [ Extra.idr ]
-- Module      : String.Extra
-- Description : A port of Elm's string-extra package to Idris.
-- Copyright   : string-extra Copyright (c) 2016, Elm Community
--               String.Extra Copyright (c) 2016, Eric Bailey
-- License     : BSD-3
-- Link        : https://github.com/elm-community/string-extra
-- --------------------------------------------------------------------- [ EOH ]
module String.Extra

import Prelude.Strings

%access export

-- -------------------------------------------------------------- [ Formatting ]

-- NOTE: This is a bit like Clojure's cond->.
syntax "cond$" [x] [b] [f] = if b then x else f x

||| Trim the whitespace of both sides of the string and compress repeated
||| whitespace internally to a single character.
|||
||| ```idris example
||| clean " The   quick brown   fox    "
||| ```
clean : String -> String
clean str = trim (go str)
  where
    go xs with (strM xs)
      go "" | StrNil = ""
      go (strCons x xs) | StrCons _ _
         = strCons x (assert_total (clean (cond$ xs (isSpace x) ltrim)))

||| Remove surrounding strings from another string.
|||
||| ```idris example
||| unsurround "foo" "foobarfoo"
||| ```
unsurround : String -> String -> String
unsurround wrap string =
  if isPrefixOf wrap string && isPrefixOf wrap string
     then let n = length wrap in
              pack (reverse (drop n (reverse (drop n (unpack string)))))
     else string

||| Remove quotes that surround a string.
|||
||| ```idris example
||| unquote "\"foo\""
||| ```
||| ```idris example
||| unquote "\"foo\"bar\""
||| ```
unquote : String -> String
unquote = unsurround "\""

||| docstring
|||
||| ```idris example
||| unindent "  Hello\n    World"
||| ```
||| ```idris example
||| unindent "\t\tHello\n\t\t\t\tWorld"
||| ```
unindent : String -> String
unindent s = let lines = lines' (unpack s) in
                 pack (unlines' (map (drop (minLead lines)) lines))
  where
    countIndent : Nat -> List Char -> Nat
    countIndent n []           = n
    countIndent n (' ' :: xs)  = countIndent (S n) xs
    countIndent n ('\t' :: xs) = countIndent (S n) xs
    countIndent n (_ :: xs)    = n

    isNotIndent : Char -> Bool
    isNotIndent c = ' ' /= c && '\t' /= c

    minimum : Ord a => List a -> Maybe a
    minimum [] = Nothing
    minimum (x :: xs) = Just $ foldr min x xs

    minLead : List (List Char) -> Nat
    minLead = fromMaybe 0 . minimum .
              map (countIndent 0) .
              filter (any isNotIndent)

||| Given a string longer than `howLong`, truncate it and append the `append`
||| string such that the resulting string is exactly `howLong` in length.
||| Return the string if its length is less than or equal to `howLong`.
|||
||| ```idris example
||| ellipsisWith 5 " .." "Hello World"
||| ```idris example
||| ellipsisWith 10 " .."  "Hello World"
||| ```idris example
||| ellipsisWith 10 " .." "Hello"
||| ```
||| ```idris example
||| ellipsisWith 8 " .." "Hello World"
||| ```
|||
||| @ howLong maximum length of the resulting string
||| @ append string to append to truncated strings, e.g. `"..."`
||| @ smaller proof that `(length append)` is less than or equal to `howLong`
ellipsisWith : (howLong : Nat) -> (append : String) -> String ->
               {auto smaller : LTE (length append) howLong} ->
               String
ellipsisWith howLong append string =
  if length string <= howLong
     then string
     else substr 0 (howLong - (length append)) string ++ append

||| Given a string longer than `howLong`, truncate it and append three dots such
||| that the resulting string is exactly `howLong` in length.
||| Return the string if its length is less than or equal to `howLong`.
|||
||| ```idris example
||| ellipsis 5 "Hello World"
||| ```
||| ```idris example
||| ellipsis 10 "Hello World"
||| ```
||| ```idris example
||| ellipsis 10 "Hello"
||| ```
||| ```idris example
||| ellipsis 8 "Hello World"
||| ```
|||
||| @ howLong maximum length of the resulting string
||| @ smaller proof that 3 is less than or equal to `howLong`
ellipsis : (howLong : Nat) -> String ->
           {auto smaller : LTE 3 howLong} ->
           String
ellipsis howLong = ellipsisWith howLong "..."

||| Given a string longer than `howLong`, truncate it and append three dots such
||| that the resulting string is exactly `howLong` in length.
||| Return the string if its length is less than or equal to `howLong`.
|||
||| Unlike `ellipsis`, do *not* produce unfinished words, instead, collect as
||| many complete words as meet the length constraint.
|||
||| Additionally, remove any trailing whitespace and punctuation at the end of
||| truncated string.
|||
||| ```idris example
||| softEllipsis 5 "Hello, World" == "Hello..."
||| ```
||| ```idris example
||| softEllipsis 8 "Hello, World" == "Hello..."
||| ```
||| ```idris example
||| softEllipsis 15 "Hello, cruel world" == "Hello, cruel..."
||| ```
||| ```idris example
||| softEllipsis 10 "Hello" == "Hello"
||| ```
|||
||| @ howLong maximum length of the resulting string
||| @ smaller proof that 3 is less than or equal to `howLong`
softEllipsis : (howLong : Nat) -> String ->
               {auto smaller : LTE 3 howLong} ->
               String
{-
softEllipsis howLong string =
  if length string <= howLong
     then string
     else go (howLong - 3) (0, []) (words string)
  where
    pred : Char -> Bool
    pred c = isSpace c || '.' == c || ',' == c || ';' == c || ':' == c
    go : Nat -> (Nat, List String) -> List String -> String
    go max (n, ys) []
       = unwords (reverse ys) ++ "..."
    go max (n, ys) [x]
       = let x' = pack (reverse (dropWhile (pred) (reverse (unpack x)))) in
             ?rhs
    go max (n, ys) (x :: xs)
       = let m = length x in
             if n + m <= max
                then go max (n + m, x :: ys) xs
                else go max (n, ys) []
-}

-- TODO: Consider implementing stripTags.
{-
||| Remove all HTML tags from a string, preserving the text inside them.
|||
||| ```idris example
||| stripTags "a <a href=\"#\">link</a>" == "a link"
||| ```
||| ```idris example
||| stripTags "<script>alert('hello world!')</script> == "alert('hello world!')"
||| ```
stripTags : String -> String
-}

||| Given a singular string, a plural string, and number, return the number
||| followed by a space, followed by either the singular string if the number
||| was 1, or the plural string otherwise.
|||
||| ```idris example
||| pluralize "elf" "elves" 2
||| ```
||| ```idris example
||| pluralize "elf" "elves" 1
||| ```
||| ```idris example
||| pluralize "elf" "elves" 0
||| ```
pluralize : String -> String -> Nat -> String
pluralize singular plural count =
  if count == 1
     then "1 " ++ singular
     else (show count) ++ " " ++ plural

-- --------------------------------------------------------------------- [ EOF ]
