-- --------------------------------------------------------------- [ Extra.idr ]
-- Module      : String.Extra
-- Description : A port of Elm's string-extra package to Idris.
-- Copyright   : string-extra Copyright (c) 2016, Elm Community
--               String.Extra Copyright (c) 2016, Eric Bailey
-- License     : BSD-3
-- Link        : https://github.com/elm-community/string-extra
-- --------------------------------------------------------------------- [ EOH ]
||| String helper functions for Idris, inspired by Elm's string-extra.
module String.Extra

import Prelude.Strings

%access export

-- --------------------------------------------------------------- [ Splitting ]

private
dropLeft : Nat -> String -> String
dropLeft n = pack . drop n . unpack

private
breaker : Nat -> String -> List String -> List String
breaker width "" acc     = reverse acc
breaker width string acc = breaker width
                                   (dropLeft width string)
                                   (substr 0 width string :: acc)

||| Break a string into a list of strings of at most `width` characters.
|||
||| ```idris example
||| break 10 "The quick brown fox"
||| ```
||| ```idris example
||| break 2 ""
||| ```
|||
||| @ width the maximum length of the resulting strings
break : (width : Nat) -> String -> List String
break Z string     = [string]
break _ ""         = [""]
break width string = breaker width string []

||| Break a string into a list of strings of at most `width` characters, without
||| chopping words.
|||
||| ```idris example
||| softBreak 6 "The quick brown fox"
||| ```
|||
||| @ width the maximum length of the resulting strings
softBreak : (width : Nat) -> String -> List String
softBreak Z _          = []
softBreak width string = go Nothing [] string
  where
  go : Maybe String -> List String -> String -> List String
  go (Just ps) acc ""  = reverse (ps :: acc)
  go Nothing acc ""    = reverse acc
  go Nothing acc str   =
      let (w1, r1) = break isSpace str
          (s1, r2) = span isSpace r1
          str2 = w1 ++ s1 in
          if length str2 >= width
             then go Nothing (str2 :: acc) r2
             else go (Just str2) acc r2
  go (Just ps) acc str =
      let (w1, r1) = break isSpace str
          (s1, r2) = span isSpace r1
          str2 = w1 ++ s1 in
          if length str2 >= width
             then go Nothing (str2 :: ps :: acc) r2
             else let str3 = ps ++ str2 in
                      if length str3 >= width
                         then go (Just str2) (ps :: acc) r2
                         else go (Just str3) acc r2

-- -------------------------------------------------------------- [ Formatting ]

||| Trim the whitespace of both sides of the string and compress repeated
||| whitespace internally to a single character.
|||
||| ```idris example
||| clean " The   quick brown   fox    "
||| ```
clean : String -> String
clean = trim . go
  where
    go : String -> String
    go str with (strM str)
      go ""             | StrNil      = ""
      go (strCons c cs) | StrCons _ _ =
          strCons c $ assert_total $ go $ if isSpace c then ltrim cs else cs

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

||| Truncate a string and append three dots, such that the resulting string is
||| at most `howLong + 3` in length. Return the string if its length is less
||| than or equal to `howLong`.
|||
||| Unlike `ellipsis`, do *not* produce unfinished words, instead, collect as
||| many complete words as meet the length constraint.
|||
||| Additionally, remove any trailing whitespace and punctuation at the end of
||| truncated string.
|||
||| ```idris example
||| softEllipsis 5 "Hello, World"
||| ```
||| ```idris example
||| softEllipsis 8 "Hello, World"
||| ```
||| ```idris example
||| softEllipsis 15 "Hello, cruel world"
||| ```
||| ```idris example
||| softEllipsis 10 "Hello"
||| ```
|||
||| @ howLong maximum length of the resulting string
softEllipsis : (howLong : Nat) -> String -> String
softEllipsis howLong string =
    if length string <= howLong
       then string
       else fromMaybe "" $
            (flip (++) "...") . dropTrailing <$>
            head' (softBreak howLong string)
  where
    p : Char -> Bool
    p c = isSpace c || '.' == c || ',' == c || ';' == c || ':' == c
    dropTrailing : String -> String
    dropTrailing = reverse . snd . span p . reverse

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
