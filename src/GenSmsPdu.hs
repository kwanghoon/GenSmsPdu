{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module GenSmsPdu where

{-
IDEA:

TP_UD depends on TP_UDHI and TP_DCS. Hence the current interface definition for toBit, BitRep a => [Int] -> a, is not enought. Something like BitRep a b => [Int] -> b -> a is required. Normally, BitRep a () is enought. Regarding TP_UD, BitRep TP_UD (TP_UDHI * TP_DCS) is required. 

TP_VP also shows similar phenomena. TP_VP depends on TP_VPF. BitRep TP_UD TP_VP TP_VPF is good enought. 

AddrValue is a variable length field. The length is defined by AddrLength field.

TP_CDL specifies the length of TP_CD.


0) Explicit manipulation of bits

   [ b7,b6,b5,b4,b3,b2,b1,b0,b7',b6',b5',b4',b3',b2',b1',b0', ... ]

1) pattern matching
   cf) show encoder/decoder written in C and compare it with Haskell version!

2) value oriented programming bits1, bits2, bits3 
3) Modular definition of encoding/decoding using instance declarations with contextual information 
4) Same idea for modularitiy is applied to random value generation
5) a collection of small pieces of utilities to parse bits
6) finding a suitable instance with a given type
7) interactive system allowing to give various queries

[Discussion]

Pros
1) QuickCheck does help to identify bugs of this Haskell program itself!

ex)
SMS_Submit_Report_for_RP_NAck (TP_UDHI False) (TP_FCS 166) (TP_PI True 13 False True False) (TP_SCTS 75 68 9 30 55 7 72) Nothing (Just (TP_DCS_General True True Class1 UCS2_16Bit)) Nothing Nothing
-> 
01A6EA7568093055077236
sanity test: False
SMS_Submit_Report_for_RP_NAck (TP_UDHI False) (TP_FCS 166) (TP_PI True 13 False True False) (TP_SCTS 75 68 9 30 55 7 72) Nothing (Just (TP_DCS_General True True Class2 CS_8Bit)) Nothing Nothing
[]

We have only to look at the decoding/encoding functions for TP_DCS_General, particularly for Class and Character encoding.

2) Interactive environment by GHCi => Allow a modular test by running smaller pieces of encoding and decoding functions. 

*GenSmsPdu> encode TP_PID_Bits7_6_SC_specific_use (TP_PID_Bits5_0_SC_Specific_Use 87)
[0,1,0,1,1,1]
*GenSmsPdu> decode TP_PID_Bits7_6_SC_specific_use [0,1,0,1,1,1]

3) Some ambiguity of SMS PDU specification

   - TP_PI (1 octet) is optional. What does that mean?
   - TP_UDHI (1 bit) is also declared to be optional. What does this mean?

Cons
1) The definition of valid requires to know both Haskell and SMS. But no one here in MC R&D center knows Haskell. How can we separate Haskell from SMS? The separation would be a good idea to make QuickCheck popular and to be maintainable.

2) Places that types cann't be effective

[0,1] ++ [b5,b4] ++ encode () cs ++ encode () msgclass 

  vs.

[0,1] ++ [b5,b4] ++ encode () msgclass ++ encode () cs 


KNOWN BUGS

 - 2010/02/26 [OPEN] : A bit longer PDUs are generated.
 - 2010/02/26 [OPEN] : Seven octets are mandatory for Enhanced VP, but shoter ones are generated. 
 - 2010/02/26 [OPEN] : The length of UCS2 16bits in PDU is defined to be the unit of octets, not to be the unit of a 16 bit character.

 - 2010/02/26 [FIXED] : The following exception. It seems to be relevant to the long PDU bug.

     encode (TP_UDHI False, UCS2_16Bit) (TP_UD_NoUDH 138 "You'll never see all the places, or read all the books, but fortunately, they're not all recommended.-- Mark Twain, \"Tom Sawyer\"Q:\tHow man")
*** Exception: [intToBits8] Too big or too small for 8bits: 276

-}

import Data.Char
import Data.Maybe
import Control.Monad
import System.Random
import System.IO
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Random

class Variant a where
    valid   :: Gen a
    invalid :: Gen a

instance Variant a => Arbitrary a where
    arbitrary = oneof [valid, invalid]

instance Variant Bool where
    valid = elements [ False, True ]
    invalid = valid

instance Variant a => Variant (Maybe a) where
    valid = oneof [ liftM Just valid, return Nothing ]
    invalid = valid

-- proper1 f = liftM f valid
-- proper2 f = liftM2 f valid valid
-- proper3 f = liftM3 f valid valid valid
-- proper4 f = liftM4 f valid valid valid valid
-- proper5 f = liftM5 f valid valid valid valid valid


-- bad1 f = liftM f invalid
-- bad2 f = oneof $ tail [ liftM2 f g1 g2 | g1 <- [valid, invalid], g2 <- [valid, invalid] ]
-- bad3 f = oneof $ tail [ liftM3 f g1 g2 g3 | g1 <- [valid, invalid], g2 <- [valid, invalid], g3 <- [valid, invalid] ]
-- bad4 f = oneof $ tail [ liftM4 f g1 g2 g3 g4 | g1 <- [valid, invalid], g2 <- [valid, invalid], g3 <- [valid, invalid], g4 <- [valid, invalid] ]
-- bad5 f = oneof $ tail [ liftM5 f g1 g2 g3 g4 g5 | g1 <- [valid, invalid], g2 <- [valid, invalid], g3 <- [valid, invalid], g4 <- [valid, invalid], g5 <- [valid, invalid] ]

--
class BitRep a b where
   encode :: b -> a -> [Int]
   decode :: b -> [Int] -> (a, [Int])

instance (Show a, Show b, BitRep a b) => BitRep (Maybe a) (Bool, b) where
   encode (False, b) Nothing  = []
   encode (True,  b) (Just a) = encode b a
   encode (flag,  b) a
      = error ("[encode] Maybe : "++ show (flag,b) ++ ", " ++ show a)

   decode (False, b) bits = (Nothing, bits)
   decode (True,  b) bits = let (a, bits') = decode b bits
                            in  (Just a, bits')

-- Utilities

-- 16 bits
intToBits16 i 
   | 0 <= i &&  i <= 65536-1
      = let [b15,b14,b13,b12,b11,b10,b9,b8] = intToBits8 (i `div` 2^8)
            [b7,b6,b5,b4,b3,b2,b1,b0] = intToBits8 (i `mod` 2^8)
        in
            [b15,b14,b13,b12,b11,b10,b9,b8,b7,b6,b5,b4,b3,b2,b1,b0] 
   | otherwise = error ("[intToBits16] Too big or too small for 16bits: " ++ show i)

bits16ToInt (b15:b14:b13:b12:b11:b10:b9:b8:b7:b6:b5:b4:b3:b2:b1:b0:bits)
      = bits8ToInt [b15,b14,b13,b12,b11,b10,b9,b8] * 2^8 +
        bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]
bits16ToInt bits
   = error ("[bits16ToInt] More than or less than 16 bits:" ++ show bits)

-- 8 bits
intToBits8 i
   | 0 <= i && i <= 256-1 = [b7,b6,b5,b4,b3,b2,b1,b0] 
   | otherwise = error ("[intToBits8] Too big or too small for 8bits: "
                            ++ show i)
      where 
         [b7,b6,b5,b4] = intToBits4 (i `div` 2^4)
         [b3,b2,b1,b0] = intToBits4 (i `mod` 2^4)

bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]
   = bits4ToInt [b7,b6,b5,b4] * 2^4 + bits4ToInt [b3,b2,b1,b0]
bits8ToInt bits
   = error ("[bits8ToInt] More than or less than 8 bits:" ++ show bits)

-- 4 bits
intToBits4 i 
   | 0 <= i && i <= 16-1 = [b3,b2,b1,b0]
   | otherwise = error ("[intToBits4] Too big or too small for " ++ show i)
      where
        b3 = i `div` 2^3
        b2 = (i - b3 * 2^3) `div` 2^2
        b1 = (i - b3 * 2^3 - b2 * 2^2) `div` 2^1
        b0 = (i - b3 * 2^3 - b2 * 2^2 - b1 * 2^1) `div` 2^0

bits4ToInt [b3,b2,b1,b0] = b3 * 2^3 + b2 * 2^2 + b1 * 2^1 + b0 * 2^0
bits4ToInt bits = error ("[bits4ToInt] " ++ show bits)

hexdigitToBits4 '0' = [0,0,0,0]
hexdigitToBits4 '1' = [0,0,0,1]
hexdigitToBits4 '2' = [0,0,1,0]
hexdigitToBits4 '3' = [0,0,1,1]
hexdigitToBits4 '4' = [0,1,0,0]
hexdigitToBits4 '5' = [0,1,0,1]
hexdigitToBits4 '6' = [0,1,1,0]
hexdigitToBits4 '7' = [0,1,1,1]
hexdigitToBits4 '8' = [1,0,0,0]
hexdigitToBits4 '9' = [1,0,0,1]
hexdigitToBits4 'a' = [1,0,1,0]
hexdigitToBits4 'b' = [1,0,1,1]
hexdigitToBits4 'c' = [1,1,0,0]
hexdigitToBits4 'd' = [1,1,0,1]
hexdigitToBits4 'e' = [1,1,1,0]
hexdigitToBits4 'f' = [1,1,1,1]
hexdigitToBits4 'A' = [1,0,1,0]
hexdigitToBits4 'B' = [1,0,1,1]
hexdigitToBits4 'C' = [1,1,0,0]
hexdigitToBits4 'D' = [1,1,0,1]
hexdigitToBits4 'E' = [1,1,1,0]
hexdigitToBits4 'F' = [1,1,1,1]
hexdigitToBits4 c = error ("[hexdigitToBits4] c : " ++ show c)

bits4ToHexdigit [0,0,0,0] = '0'
bits4ToHexdigit [0,0,0,1] = '1'
bits4ToHexdigit [0,0,1,0] = '2'
bits4ToHexdigit [0,0,1,1] = '3'
bits4ToHexdigit [0,1,0,0] = '4'
bits4ToHexdigit [0,1,0,1] = '5'
bits4ToHexdigit [0,1,1,0] = '6'
bits4ToHexdigit [0,1,1,1] = '7'
bits4ToHexdigit [1,0,0,0] = '8'
bits4ToHexdigit [1,0,0,1] = '9'
bits4ToHexdigit [1,0,1,0] = 'A'
bits4ToHexdigit [1,0,1,1] = 'B'
bits4ToHexdigit [1,1,0,0] = 'C'
bits4ToHexdigit [1,1,0,1] = 'D'
bits4ToHexdigit [1,1,1,0] = 'E'
bits4ToHexdigit [1,1,1,1] = 'F'
bits4ToHexdigit bits = error ("[bits4ToHexdigit] bits : " ++ show bits)

-- GSM 7bit
bytesToGsm7bit bytes = 
   let
      is7bit c = 0 <= Data.Char.ord c && Data.Char.ord c <= 127

      mkOctetList (b0:b1:b2:b3:b4:b5:b6:b7:therest) = b7:b6:b5:b4:b3:b2:b1:b0 : mkOctetList therest
      mkOctetList (b0:b1:b2:b3:b4:b5:b6:[])         = 0:b6:b5:b4:b3:b2:b1:b0 : []
      mkOctetList (b0:b1:b2:b3:b4:b5:[])            = 0:0:b5:b4:b3:b2:b1:b0 : []
      mkOctetList (b0:b1:b2:b3:b4:[])               = 0:0:0:b4:b3:b2:b1:b0 : []
      mkOctetList (b0:b1:b2:b3:[])                  = 0:0:0:0:b3:b2:b1:b0 : []
      mkOctetList (b0:b1:b2:[])                     = 0:0:0:0:0:b2:b1:b0 : []
      mkOctetList (b0:b1:[])                        = 0:0:0:0:0:0:b1:b0 : []
      mkOctetList (b0:[])                           = 0:0:0:0:0:0:0:b0 : []
      mkOctetList []                                = []
   in
   if all is7bit bytes
   then mkOctetList $ 
            reverse $ 
            concat  $ 
            reverse $
            map (drop 1 . intToBits8 . Data.Char.ord) bytes
   else error ("[bytesToGsm7bit] bytes=" ++ show bytes)

mkOctetList [] = []
mkOctetList (b7:b6:b5:b4:b3:b2:b1:b0:bits) = [b7,b6,b5,b4,b3,b2,b1,b0] : mkOctetList bits
mkOctetList bits = error ("[gsm7bitToBytes mkOctetList] " ++ show bits)

gsm7bitToBytes len bits = gsm7bitToBytes' len (concat $ map reverse bits8s) []
   where

      bits8s = mkOctetList bits

      gsm7bitToBytes' 0   (0:0:0:0:0:0:0:bits) accu = (accu, bits)
      gsm7bitToBytes' 0   (0:0:0:0:0:0:bits) accu = (accu, bits)
      gsm7bitToBytes' 0   (0:0:0:0:0:bits) accu = (accu, bits)
      gsm7bitToBytes' 0   (0:0:0:0:bits) accu = (accu, bits)
      gsm7bitToBytes' 0   (0:0:0:bits) accu = (accu, bits)
      gsm7bitToBytes' 0   (0:0:bits) accu = (accu, bits)
      gsm7bitToBytes' 0   (0:bits) accu = (accu, bits)
      gsm7bitToBytes' 0   bits accu = (accu, bits)
      gsm7bitToBytes' len (b0:b1:b2:b3:b4:b5:b6:bits) accu
         = gsm7bitToBytes' (len-1) bits (accu ++ [Data.Char.chr (bits8ToInt [0,b6,b5,b4,b3,b2,b1,b0])])
      gsm7bitToBytes' len bits accu
         = error ("[gsm7bitToBytes gsm7bitToBytes'] accu=" ++ show accu ++ ", len=" ++ show len ++ ", bits=" ++ show bits)

-- 8bit
bytesToCS8bit bytes =
   if and (map (\i -> 0<=i && i<=2^8-1) (map Data.Char.ord bytes))
   then concat $ map (intToBits8 . Data.Char.ord)  bytes
   else error ("[bytesToCS8bit] " ++ bytes)

cs8bitToBytes len bits = cs8bitToBytes' len bits
   where
      cs8bitToBytes' 0 bits = ([], bits)
      cs8bitToBytes' n (b7:b6:b5:b4:b3:b2:b1:b0:bits) 
         = let (bytes', bits') = cs8bitToBytes' (n-1) bits
           in (Data.Char.chr (bits8ToInt (b7:b6:b5:b4:b3:b2:b1:b0:[]))
               : bytes', bits')
      cs8bitToBytes' _ _
         = error ("[cs8bitToBytes] len=" ++ show len ++ ", " ++ show bits)

-- UCS2         
bytesToUCS16bit bytes =
   if and (map (\i -> 0<=i && i<=2^16-1) (map Data.Char.ord bytes))
   then concat $ map (intToBits16 . Data.Char.ord) bytes
   else error ("[bytesToCS16bit] " ++ bytes)

ucs16bitToBytes len bits = ucs16bitToBytes' len bits
   where 
      ucs16bitToBytes' 0 bits = ([], bits)
      ucs16bitToBytes' n (b15:b14:b13:b12:b11:b10:b9:b8:b7:b6:b5:b4:b3:b2:b1:b0:bits) 
         = let (bytes', bits') = ucs16bitToBytes' (n-1) bits
           in (Data.Char.chr (bits16ToInt (b15:b14:b13:b12:b11:b10:b9:b8:b7:b6:b5:b4:b3:b2:b1:b0:[])) : bytes', bits')
      ucs16bitToBytes' _ _
         = error ("[ucs16bitToBytes] len=" ++ show len ++ ", " ++ show bits)

-- 
bitsToHexString bits = bitsToHexString' bits
   where
      bitsToHexString' (b7:b6:b5:b4:b3:b2:b1:b0:bits) 
         = bits4ToHexdigit [b7,b6,b5,b4]
           : bits4ToHexdigit [b3,b2,b1,b0]
           : bitsToHexString' bits
      bitsToHexString' [] = []
      bitsToHexString' bits'
         = error ("[bitsToHexString] " ++ show (length bits') ++ " : " ++ show bits) 

hexStringToBits [] = []
hexStringToBits (c:hstr) = hexdigitToBits4 c : hexStringToBits hstr

-- Random texts

getRandomText len = getRandomText' ""
   where
      getRandomText' accu_str = 
         do { i <- choose (0,length text_samples-1);
              let accu_str' = accu_str ++ (text_samples !! i) in
              if length accu_str' < len then getRandomText' accu_str'
              else return (take len accu_str')
            }

text_samples = [
   "You will soon forget this.",
   "Persons attempting to find a motive in this narrative will be prosecuted; persons attempting to find a moral in it will be banished; persons attempting to find a plot in it will be shot.  By Order of the Author",
   "-- Mark Twain, \"Tom Sawyer\"",
   "Bank error in your favor.  Collect $200.",
   "You are capable of planning your future.",
   "The mind is its own place, and in itself Can make a Heav'n of Hell, a Hell of Heav'n.",
   "-- John Milton",
   "I was gratified to be able to answer promptly, and I did. I said I didn't know.",
   "-- Mark Twain",
   "You dialed 5483.",
   "Don't worry so loud, your roommate can't think.",
   "You'll never see all the places, or read all the books, but fortunately, they're not all recommended.",
   "Q: How many journalists does it take to screw in a light bulb?\nA: Three.  One to report it as an inspired government program to bring\nlight to the people, one to report it as a diabolical government plot\nto deprive the poor of darkness, and one to win a Pulitzer prize for\nreporting that Electric Company hired a light bulb-assassin to break\nthe bulb in the first place.",
   "Truth will out this morning.  (Which may really mess things up.)",
   "Soap and education are not as sudden as a massacre, but they are more deadly in the long run.",
   "-- Mark Twain",
   "Q:\tHow many DEC repairman does it take to fix a flat?,\nA:\tFive; four to hold the car up and one to swap tires.",
   "Q:\tHow long does it take?\nA:\tIt's indeterminate.\nIt will depend upon how many flats they've brought with them.",
   "Q:\tWhat happens if you've got TWO flats?\nA:\tThey replace your generator.",
   "As to the Adjective: when in doubt, strike it out.",
   "-- Mark Twain, \"Pudd'nhead Wilson's Calendar\"",
   "You're not my type.  For that matter, you're not even my species!!!",
   "Your aims are high, and you are capable of much.",
   "Q:\tWhat's the difference between USL and the Titanic?\nA:\tThe Titanic had a band.",
   "The human race has one really effective weapon, and that is laughter.",
   "-- Mark Twain",
   "You look like a million dollars.  All green and wrinkled.",
   "\"I understand this is your first dead client,\" Sabian was saying.  The\nabsurdity of the statement made me want to laugh but they don't call me\nDeadpan Allie and lie.",
   "-- Pat Cadigan, \"Mindplayers\"",
   "The Least Perceptive Literary Critic\n\tThe most important critic in our field of study is Lord Halifax.  A most individual judge of poetry, he once invited Alexander Pope round to give a public reading of his latest poem.\n\tPope, the leading poet of his day, was greatly surprised when Lord Halifax stopped him four or five times and said, \"I beg your pardon, Mr. Pope, but there is something in that passage that does not quite please me.\"\n\tPope was rendered speechless, as this fine critic suggested sizeable\nand unwise emendations to his latest masterpiece.  \"Be so good as to mark\nthe place and consider at your leisure.  I'm sure you can give it a better turn.\"\n\tAfter the reading, a good friend of Lord Halifax, a certain Dr.\nGarth, took the stunned Pope to one side.  \"There is no need to touch the\nlines,\" he said.  \"All you need do is leave them just as they are, call on\nLord Halifax two or three months hence, thank him for his kind observation\non those passages, and then read them to him as altered.  I have known him\nmuch longer than you have, and will be answerable for the event.\"\n\tPope took his advice, called on Lord Halifax and read the poem\nexactly as it was before.  His unique critical faculties had lost none of\ntheir edge.  \"Ay\", he commented, \"now they are perfectly right.  Nothing can\nbe better.\"",
   "-- Stephen Pile, \"The Book of Heroic Failures\"",
   "Avoid reality at all costs.",
   "You will have good luck and overcome many hardships.",
   "You will triumph over your enemy.",
   "Your talents will be recognized and suitably rewarded.",
   "You are dishonest, but never to the point of hurting a friend.",
   "It's all in the mind, ya know.",
   "Your supervisor is thinking about you.",
   "Your motives for doing whatever good deed you may have in mind will be\nmisinterpreted by somebody.",
   "I don't know half of you half as well as I should like; and I like less\nthan half of you half as well as you deserve.",
   "-- J. R. R. Tolkien",
   "Life is to you a dashing and bold adventure.",
   "A hundred years from now it is very likely that [of Twain's works] \"The\nJumping Frog\" alone will be remembered.",
   "-- Harry Thurston Peck (Editor of \"The Bookman\"), January 1901.",
   "You will get what you deserve.",
   "You are so boring that when I see you my feet go to sleep.",
   "You will win success in whatever calling you adopt.",
   "Q:\tHow many psychiatrists does it take to change a light bulb?\nA:\tOnly one, but it takes a long time, and the light bulb has\n to really want to change.",
   "Someone is speaking well of you.",
   "How unusual!\n\nQ:\tWhy did the germ cross the microscope?\nA:\tTo get to the other slide.",
   "Your sister swims out to meet troop ships."
  ]

getRandomPhoneNumber len = getRandomPhoneNumber' ""
   where
      getRandomPhoneNumber' accu_str = 
         do { digit <- elements bcd_digits;
              let accu_str' = accu_str ++ [digit] in
              if length accu_str' < len
              then getRandomPhoneNumber' accu_str'
              else return (take len accu_str')
            }

bcd_digits = ['0','1','2','3','4','5','6','7','8','9', '#','*','a', 'b', 'c']

bitsToBCDDigits [0,0,0,0] = '0'
bitsToBCDDigits [0,0,0,1] = '1'
bitsToBCDDigits [0,0,1,0] = '2'
bitsToBCDDigits [0,0,1,1] = '3'
bitsToBCDDigits [0,1,0,0] = '4'
bitsToBCDDigits [0,1,0,1] = '5'
bitsToBCDDigits [0,1,1,0] = '6'
bitsToBCDDigits [0,1,1,1] = '7'
bitsToBCDDigits [1,0,0,0] = '8'
bitsToBCDDigits [1,0,0,1] = '9'
bitsToBCDDigits [1,0,1,0] = '#'
bitsToBCDDigits [1,0,1,1] = '*'
bitsToBCDDigits [1,1,0,0] = 'a'
bitsToBCDDigits [1,1,0,1] = 'b'
bitsToBCDDigits [1,1,1,0] = 'c'
bitsToBCDDigits bits = error ("[bitsToBCDDigits] " ++ show bits)


bcdDigitsToBits '0' = [0,0,0,0]
bcdDigitsToBits '1' = [0,0,0,1]
bcdDigitsToBits '2' = [0,0,1,0]
bcdDigitsToBits '3' = [0,0,1,1]
bcdDigitsToBits '4' = [0,1,0,0]
bcdDigitsToBits '5' = [0,1,0,1]
bcdDigitsToBits '6' = [0,1,1,0]
bcdDigitsToBits '7' = [0,1,1,1]
bcdDigitsToBits '8' = [1,0,0,0]
bcdDigitsToBits '9' = [1,0,0,1]
bcdDigitsToBits '#' = [1,0,1,0]
bcdDigitsToBits '*' = [1,0,1,1]
bcdDigitsToBits 'a' = [1,1,0,0]
bcdDigitsToBits 'b' = [1,1,0,1]
bcdDigitsToBits 'c' = [1,1,1,0]
bcdDigitsToBits bits = error ("[bcdDigitsToBits] " ++ show bits)

{- 3GPP TS23.040 v6.7.0 -}

--------------------------------------------------------------------------------
-- Address fields
--------------------------------------------------------------------------------
data AddrFields = AddrFields AddrLen TypeOfAddr AddrValue
     deriving (Show,Eq)

instance BitRep AddrFields a where
   encode _ (AddrFields addrlen toa addrvalue)
      = encode () addrlen ++ encode () toa ++ encode addrlen addrvalue

   decode _ bits
      = let (addrlen, bits1) = decode () bits
            (toa, bits2) = decode () bits1
            (addrval, bits3) = decode addrlen bits2
        in  (AddrFields addrlen toa addrval, bits3)

instance Variant AddrFields where
   valid = liftM3 AddrFields valid valid valid `suchThat`
             (\(AddrFields (AddrLen len) toa (AddrValue s))
                  -> len == length s)
   invalid = valid

--------------------------------------------------------------------------------
-- Address Length
--------------------------------------------------------------------------------
data AddrLen = AddrLen Int {- 8bits -}
     deriving (Show,Eq)

instance BitRep AddrLen a where
   encode _ (AddrLen i) 
      | 0 <= i && i <= 256 = intToBits8 i
      | otherwise = error ("[encode] AddrLen: " ++ show i)

   decode _ (b7:b6:b5:b4:b3:b2:b1:b0:bits) = (AddrLen (bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]), bits)
   decode _ bits = error ("[decode] AddrLen : " ++ show bits)

instance Variant AddrLen where
   valid   = do len <- choose (0, 10 * 2)
                return (AddrLen len)
   invalid = valid

--------------------------------------------------------------------------------
-- Type of Address
--------------------------------------------------------------------------------
data TypeOfAddr = TypeOfAddr TypeOfNum NumberingPlanIdentification
     deriving (Show,Eq)

instance BitRep TypeOfAddr a where
   encode _ (TypeOfAddr ton npi) = [1] ++ (encode () ton) ++ (encode () npi)

   decode _ (1:bits) =
      let (ton, bits1) = decode () bits
          (npi, bits2) = decode () bits1
      in  (TypeOfAddr ton npi, bits2)
   decode _ bits = error ("[decode] TypeOfAddr : " ++ show bits)

instance Variant TypeOfAddr where
   valid   = liftM2 TypeOfAddr valid valid
   invalid = valid

--------------------------------------------------------------------------------
-- Type of Number
--------------------------------------------------------------------------------
data TypeOfNum =
     TON_Unknown                  {- 000 -}
   | TON_Internation_number       {- 001 -}
   | TON_National_number          {- 010 -}
   | TON_Network_specific_number  {- 011 -}
   | TON_Subscriber_number        {- 100 -}
   | TON_Alphanumeric_gsm7bit     {- 101 -}
   | TON_Abbreviated_number       {- 110 -}
   | TON_Reserved                 {- 111 -}
     deriving (Show, Eq)

instance BitRep TypeOfNum a where
   encode _ TON_Unknown                 = [0,0,0]
   encode _ TON_Internation_number      = [0,0,1]
   encode _ TON_National_number         = [0,1,0]
   encode _ TON_Network_specific_number = [0,1,1]
   encode _ TON_Subscriber_number       = [1,0,0]
   encode _ TON_Alphanumeric_gsm7bit    = [1,0,1]
   encode _ TON_Abbreviated_number      = [1,1,0]
   encode _ TON_Reserved                = [1,1,1]

   decode _ (0:0:0:bits) = (TON_Unknown, bits)
   decode _ (0:0:1:bits) = (TON_Internation_number, bits)
   decode _ (0:1:0:bits) = (TON_National_number, bits) 
   decode _ (0:1:1:bits) = (TON_Network_specific_number, bits)
   decode _ (1:0:0:bits) = (TON_Subscriber_number, bits)
   decode _ (1:0:1:bits) = (TON_Alphanumeric_gsm7bit, bits)
   decode _ (1:1:0:bits) = (TON_Abbreviated_number, bits)
   decode _ (1:1:1:bits) = (TON_Reserved, bits)
   decode _ bits = error ("[decode] TypeOfNum : " ++ show bits)

instance Variant TypeOfNum where
   valid = elements [ TON_Unknown, TON_Internation_number,
                   TON_National_number, TON_Network_specific_number,
                   TON_Subscriber_number, TON_Alphanumeric_gsm7bit,
                   TON_Abbreviated_number, TON_Reserved 
                 ]
   invalid = valid

--------------------------------------------------------------------------------
-- Numbering Plan Identification
--------------------------------------------------------------------------------
data NumberingPlanIdentification = 
     NPI_Unknown                        {- 0000 -}
   | NPI_ISDN_Tel_numbering_plan        {- 0001 -}
   | NPI_Data_numbering_plan            {- 0011 -}
   | NPI_Telex_numbering_plan           {- 0100 -}
   | NPI_Service_center_specific_plan1  {- 0101 -}
   | NPI_Service_center_specific_plan2  {- 0102 -}
   | NPI_National_numbering_plan        {- 1000 -}
   | NPI_Private_numbering_plan         {- 1001 -}
   | NPI_ERMES_numbering_plan           {- 1010 -}
   | NPI_Reserved Int                   {- 1111 and the rest values -}
     deriving (Show, Eq)

instance BitRep NumberingPlanIdentification a where
   encode _ NPI_Unknown                       = [0,0,0,0]
   encode _ NPI_ISDN_Tel_numbering_plan       = [0,0,0,1]
   encode _ NPI_Data_numbering_plan           = [0,0,1,1]
   encode _ NPI_Telex_numbering_plan          = [0,1,0,0]
   encode _ NPI_Service_center_specific_plan1 = [0,1,0,1]
   encode _ NPI_Service_center_specific_plan2 = [0,1,1,0]
   encode _ NPI_National_numbering_plan       = [1,0,0,0]
   encode _ NPI_Private_numbering_plan        = [1,0,0,1]
   encode _ NPI_ERMES_numbering_plan          = [1,0,1,0]
   encode _ (NPI_Reserved i)
      | 0 <= i && i <= 15 && i `elem` [2,7,11,12,13,14,15] = drop 4 (intToBits8 i)
      | otherwise = error ("[encode] NumberingPlanIdentification :" ++ show i)

   decode _ (0:0:0:0:bits) = (NPI_Unknown, bits) 
   decode _ (0:0:0:1:bits) = (NPI_ISDN_Tel_numbering_plan, bits)
   decode _ (0:0:1:1:bits) = (NPI_Data_numbering_plan, bits)
   decode _ (0:1:0:0:bits) = (NPI_Telex_numbering_plan, bits)
   decode _ (0:1:0:1:bits) = (NPI_Service_center_specific_plan1, bits)
   decode _ (0:1:1:0:bits) = (NPI_Service_center_specific_plan2, bits)
   decode _ (1:0:0:0:bits) = (NPI_National_numbering_plan, bits)
   decode _ (1:0:0:1:bits) = (NPI_Private_numbering_plan, bits)
   decode _ (1:0:1:0:bits) = (NPI_ERMES_numbering_plan, bits)
   decode _ (b3:b2:b1:b0:bits) = (NPI_Reserved (bits8ToInt ([0,0,0,0]++[b3,b2,b1,b0])), bits)
   decode _ bits = error ("[decode] NumberingPlanIdentification : " ++ show bits)

instance Variant NumberingPlanIdentification where
   valid =
      let gen1 = elements [ NPI_Unknown, NPI_ISDN_Tel_numbering_plan,
                    NPI_Data_numbering_plan, NPI_Telex_numbering_plan,
                    NPI_Service_center_specific_plan1, NPI_Service_center_specific_plan2,
                    NPI_National_numbering_plan, NPI_Private_numbering_plan,
                    NPI_ERMES_numbering_plan]
          gen2 = liftM NPI_Reserved (elements [2,7,11,12,13,14,15])
      in frequency [(20,gen1), (1,gen2)]

   invalid = valid

--------------------------------------------------------------------------------
-- Address Value
--------------------------------------------------------------------------------
{- TBD:

Assumption:
  1) each character of the string is a hexa digit.
  2) The length of the string must be even so that each pair of the characters will be one octet.

-}

data AddrValue = AddrValue String
     deriving (Show, Eq)

instance BitRep AddrValue AddrLen where
   encode (AddrLen len) (AddrValue s)
      | len == length s
          = let f (high_digit:low_digit:ss) = bcdDigitsToBits low_digit ++ 
                                              bcdDigitsToBits high_digit ++ 
                                              f ss
                f [single_digit] = [1,1,1,1] ++ bcdDigitsToBits single_digit
                f []             = []
            in f s 
      | otherwise = error ("[encode] AddrValue string : " ++ show s 
                               ++ " whose length is " ++ show (length s))

   decode (AddrLen len) bits = 
      let toStr 0 bits = ([], bits)
          toStr i (b7:b6:b5:b4:b3:b2:b1:b0:bits)
             | i>=2 = let (hs,bits') = toStr (i-2) bits
                      in  (bitsToBCDDigits [b3,b2,b1,b0]
                          : bitsToBCDDigits [b7,b6,b5,b4]
                          : hs, bits')
             | i==1 = (bitsToBCDDigits [b3,b2,b1,b0] : [], bits)
          toStr i bits = error ("[decode] AddrValue : " ++ show i 
                                    ++ ", " ++ show bits)

          (hs, bits'') = toStr len bits
      in
          (AddrValue hs, bits'')

instance Variant AddrValue where
   valid = do len <- choose (0, 10*2)
              digits  <- getRandomPhoneNumber len
              return (AddrValue digits)
   invalid = valid


--------------------------------------------------------------------------------
-- TP-Message-Type-Indicator (TP-MTI)
--------------------------------------------------------------------------------
data TP_MTI =
     SMS_DELIVER             {- 00 when SC=>MS -}
   | SMS_DELIVER_REPORT_ACK  {- 00 when SC<=MS -}
   | SMS_DELIVER_REPORT_NACK {- 00 when SC<=MS -}

   | SMS_STATUS_REPORT       {- 10 when SC=>MS -}
   | SMS_COMMAND             {- 10 when SC<=MS -}

   | SMS_SUBMIT              {- 01 when SC<=MS -}
   | SMS_SUBMIT_REPORT_ACK   {- 01 when SC=>MS -}
   | SMS_SUBMIT_REPORT_NACK  {- 01 when SC=>MS -}

   | TP_MTI_RESERVED         {- 11             -}
     deriving (Show, Eq)

data Direction = SCtoMS | MStoSC deriving (Show, Eq)

data Acknowledgement = Ack | NAck deriving (Show, Eq)

instance BitRep TP_MTI (Direction, Maybe Acknowledgement) where
   encode (SCtoMS,Nothing)   SMS_DELIVER             = [0,0]
   encode (MStoSC,Just Ack)  SMS_DELIVER_REPORT_ACK  = [0,0]
   encode (MStoSC,Just NAck) SMS_DELIVER_REPORT_NACK = [0,0]
   encode (SCtoMS,Nothing)   SMS_STATUS_REPORT       = [1,0]
   encode (MStoSC,Nothing)   SMS_COMMAND             = [1,0]
   encode (MStoSC,Nothing)   SMS_SUBMIT              = [0,1]
   encode (SCtoMS,Just Ack)  SMS_SUBMIT_REPORT_ACK   = [0,1]
   encode (SCtoMS,Just NAck) SMS_SUBMIT_REPORT_NACK  = [0,1]
   encode (_,_)              TP_MTI_RESERVED         = [1,1]
   encode dir_ack       tp_mti                  = error ("[encode] TP_MTI : " ++ show dir_ack ++ ", " ++ show tp_mti)

   decode (SCtoMS,Nothing)   (0:0:bits) = (SMS_DELIVER, bits)
   decode (MStoSC,Just Ack)  (0:0:bits) = (SMS_DELIVER_REPORT_ACK, bits)
   decode (MStoSC,Just NAck) (0:0:bits) = (SMS_DELIVER_REPORT_NACK, bits)
   decode (SCtoMS,Nothing)   (1:0:bits) = (SMS_STATUS_REPORT, bits)
   decode (MStoSC,Nothing)   (1:0:bits) = (SMS_COMMAND, bits)
   decode (MStoSC,Nothing)   (0:1:bits) = (SMS_SUBMIT, bits)
   decode (SCtoMS,Just Ack)  (0:1:bits) = (SMS_SUBMIT_REPORT_ACK, bits)
   decode (SCtoMS,Just NAck) (0:1:bits) = (SMS_SUBMIT_REPORT_NACK, bits)
   decode (_,_)              (1:1:bits) = (TP_MTI_RESERVED, bits)
   decode dir_ack            bits       = error ("[decode] TP_MTI : " ++ show dir_ack ++ ", " ++ show bits)

instance Variant TP_MTI where
   valid = elements [ SMS_DELIVER, SMS_DELIVER_REPORT_ACK, SMS_DELIVER_REPORT_NACK, SMS_STATUS_REPORT, SMS_COMMAND, SMS_SUBMIT, SMS_SUBMIT_REPORT_ACK, SMS_SUBMIT_REPORT_NACK, TP_MTI_RESERVED ]
   invalid = valid

--------------------------------------------------------------------------------
-- TP-More-Message-to-Send (TP-MMS)
--------------------------------------------------------------------------------
data TP_MMS =
     TP_MMS_More_Messages {- 0 -}
   | TP_MMS_No_More_Messages {- 1 -}
     deriving (Show, Eq)

instance BitRep TP_MMS a where
   encode _ TP_MMS_More_Messages = [0]
   encode _ TP_MMS_No_More_Messages = [1]

   decode _ (0:bits) = (TP_MMS_More_Messages, bits)
   decode _ (1:bits) = (TP_MMS_No_More_Messages, bits)
   decode _ bits = error ("[decode] TP_MMS : " ++ show bits)

instance Variant TP_MMS where
   valid = elements [ TP_MMS_More_Messages, TP_MMS_No_More_Messages ]
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Validity-Period-Format (TP-VPF)
--------------------------------------------------------------------------------
data TP_VPF =
     TP_VP_Field_Not_Present      {- 00 -}
   | TP_VP_Field_Present_Relative {- 10 -}
   | TP_VP_Field_Present_Enhanced {- 01 -}
   | TP_VP_Field_Present_Absolute {- 11 -}
     deriving (Show, Eq)

isTP_VP_Field_Not_Present TP_VP_Field_Not_Present = True
isTP_VP_Field_Not_Present _ = False

isTP_VP_Field_Present_Relative TP_VP_Field_Present_Relative = True
isTP_VP_Field_Present_Relative _ = False

isTP_VP_Field_Present_Enhanced TP_VP_Field_Present_Enhanced = True
isTP_VP_Field_Present_Enhanced _ = False

isTP_VP_Field_Present_Absolute TP_VP_Field_Present_Absolute = True
isTP_VP_Field_Present_Absolute _ = False

instance BitRep TP_VPF a where
   encode _ TP_VP_Field_Not_Present      = [0,0] 
   encode _ TP_VP_Field_Present_Relative = [1,0]
   encode _ TP_VP_Field_Present_Enhanced = [0,1]
   encode _ TP_VP_Field_Present_Absolute = [1,1]

   decode _ (0:0:bits) = (TP_VP_Field_Not_Present, bits)
   decode _ (1:0:bits) = (TP_VP_Field_Present_Relative, bits) 
   decode _ (0:1:bits) = (TP_VP_Field_Present_Enhanced, bits)
   decode _ (1:1:bits) = (TP_VP_Field_Present_Absolute, bits)
   decode _ bits = error ("[decode] TP_VPF : " ++ show bits)

instance Variant TP_VPF where
   valid = elements [ TP_VP_Field_Not_Present, TP_VP_Field_Present_Relative, TP_VP_Field_Present_Enhanced, TP_VP_Field_Present_Absolute ]
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Status-Report-Indication (TP-SRI)
--------------------------------------------------------------------------------
data TP_SRI =
     TP_SRI_No_Status_Report_Indication  {- 0 -}
   | TP_SRI_Status_Report_Indication     {- 1 -}
     deriving (Show, Eq)

instance BitRep TP_SRI a where
   encode _ TP_SRI_No_Status_Report_Indication = [0]
   encode _ TP_SRI_Status_Report_Indication    = [1]

   decode _ (0:bits) = (TP_SRI_No_Status_Report_Indication, bits)
   decode _ (1:bits) = (TP_SRI_Status_Report_Indication, bits)
   decode _ bits = error ("[decode] TP_SRI : " ++ show bits)

instance Variant TP_SRI where
   valid = elements [ TP_SRI_No_Status_Report_Indication, TP_SRI_Status_Report_Indication ] 
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Status-Report-Request (TP-SRR)
--------------------------------------------------------------------------------
data TP_SRR =
     TP_SRR_No_Status_Report_Requested    {- 0 -}
   | TP_SRR_Status_Report_Requested       {- 1 -}
     deriving (Show, Eq)

isTP_SRR_No_Status_Report_Requested TP_SRR_No_Status_Report_Requested = True
isTP_SRR_No_Status_Report_Requested _ = False

isTP_SRR_Status_Report_Requested TP_SRR_Status_Report_Requested = True
isTP_SRR_Status_Report_Requested _ = False


instance BitRep TP_SRR a where
   encode _ TP_SRR_No_Status_Report_Requested = [0]
   encode _ TP_SRR_Status_Report_Requested   = [1]

   decode _ (0:bits) = (TP_SRR_No_Status_Report_Requested, bits)
   decode _ (1:bits) = (TP_SRR_Status_Report_Requested, bits)
   decode _ bits = error ("[decode] TP_SRR : " ++ show bits)

instance Variant TP_SRR where
   valid = elements [ TP_SRR_No_Status_Report_Requested, TP_SRR_Status_Report_Requested ] 
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Message-Reference (TP-MR)
--------------------------------------------------------------------------------
data TP_MR = TP_MR Int  {- 0 to 255 -} deriving (Show,Eq)

instance BitRep TP_MR a where
   encode _ (TP_MR i)
      | 0 <= i && i <= 255 = intToBits8 i
      | otherwise = error ("[encode] TP_MR " ++ show i)


   decode _ (b7:b6:b5:b4:b3:b2:b1:b0:bits) = (TP_MR (bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]), bits)
   decode _ bits = error ("[decode] TP_MR : " ++ show bits)

instance Variant TP_MR where
   valid = liftM TP_MR (choose (0,255))
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Originating-Address (TP-OA)
--------------------------------------------------------------------------------
data TP_OA = TP_OA AddrFields 
     deriving (Show, Eq)

instance BitRep TP_OA a where
   encode _ (TP_OA addrfields) = encode () addrfields

   decode _ bits = 
      let (addrfields, bits') = decode () bits
      in (TP_OA addrfields, bits')

instance Variant TP_OA where
   valid = liftM TP_OA valid
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Destination-Address (TP-DA)
--------------------------------------------------------------------------------
data TP_DA = TP_DA AddrFields 
     deriving (Show, Eq)

instance BitRep TP_DA a where
   encode _ (TP_DA addrfields) = encode () addrfields

   decode _ bits 
      = let (addrfields,bits') = decode () bits
        in  (TP_DA addrfields, bits')

instance Variant TP_DA where
   valid = liftM TP_DA valid
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Protocol-Identifier (TP-PID)
--------------------------------------------------------------------------------
data TP_PID = TP_PID TP_PID_Bits7_6 TP_PID_Bits5_0
     deriving (Show, Eq)

instance BitRep TP_PID a where
   encode _ (TP_PID tp_pid_bits7_6 tp_pid_bits5_0)
      = encode () tp_pid_bits7_6 ++ encode tp_pid_bits7_6 tp_pid_bits5_0

   decode _ bits
      = let (tp_pid_bits7_6, bits') = decode () bits
            (tp_pid_bits5_0, bits'') = decode tp_pid_bits7_6 bits'
        in  (TP_PID tp_pid_bits7_6 tp_pid_bits5_0, bits'')

instance Variant TP_PID where
   valid = do tp_pid_bits7_6 <- valid
              tp_pid_bits5_0 <- valid `suchThat` 
                    (\tp_pid_bits5_0 ->
                        isTP_PID_Bits7_6_00 tp_pid_bits7_6
                        && isTP_PID_Bit5_Bits4_0 tp_pid_bits5_0
                     || isTP_PID_Bits7_6_01 tp_pid_bits7_6
                        && isTP_PID_Bits5_0_ tp_pid_bits5_0
                     || isTP_PID_Bits7_6_Reserved tp_pid_bits7_6
                        && isTP_PID_Bits5_0_Reserved tp_pid_bits5_0
                     || isTP_PID_Bits7_6_SC_specific_use tp_pid_bits7_6
                        && isTP_PID_Bits5_0_SC_Specific_Use tp_pid_bits5_0
                    )
              return (TP_PID tp_pid_bits7_6 tp_pid_bits5_0)
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Protocol-Identifier 7 to 6 bits
--------------------------------------------------------------------------------
data TP_PID_Bits7_6 =
     TP_PID_Bits7_6_00  {- 00 -}
   | TP_PID_Bits7_6_01  {- 01 -}
   | TP_PID_Bits7_6_Reserved           {- 10 -}
   | TP_PID_Bits7_6_SC_specific_use    {- 11 -}
     deriving (Show, Eq)

isTP_PID_Bits7_6_00 TP_PID_Bits7_6_00 = True
isTP_PID_Bits7_6_00 _ = False

isTP_PID_Bits7_6_01 TP_PID_Bits7_6_01 = True
isTP_PID_Bits7_6_01 _ = False

isTP_PID_Bits7_6_Reserved TP_PID_Bits7_6_Reserved = True
isTP_PID_Bits7_6_Reserved _ = False

isTP_PID_Bits7_6_SC_specific_use TP_PID_Bits7_6_SC_specific_use = True
isTP_PID_Bits7_6_SC_specific_use _ = False

instance BitRep TP_PID_Bits7_6 a where
   encode _ TP_PID_Bits7_6_00 = [0,0]
   encode _ TP_PID_Bits7_6_01 = [0,1]
   encode _ TP_PID_Bits7_6_Reserved          = [1,0]
   encode _ TP_PID_Bits7_6_SC_specific_use   = [1,1]

   decode _ (0:0:bits) = (TP_PID_Bits7_6_00, bits)
   decode _ (0:1:bits) = (TP_PID_Bits7_6_01, bits)
   decode _ (1:0:bits) = (TP_PID_Bits7_6_Reserved, bits)
   decode _ (1:1:bits) = (TP_PID_Bits7_6_SC_specific_use, bits)
   decode _ bits = error ("[decode] TP_PID_Bits7_6 : " ++ show bits)

instance Variant TP_PID_Bits7_6 where
   valid = elements [ TP_PID_Bits7_6_00, TP_PID_Bits7_6_01, TP_PID_Bits7_6_Reserved, TP_PID_Bits7_6_SC_specific_use ]
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Protocol-Identifier 5 to 0 bits
--------------------------------------------------------------------------------
data TP_PID_Bits5_0 =
     TP_PID_Bit5_Bits4_0 TP_PID_Bit5 TP_PID_Bits4_0
   | TP_PID_Bits5_0_ TP_PID_Bits5_0_
   | TP_PID_Bits5_0_Reserved Int        -- 6 bits
   | TP_PID_Bits5_0_SC_Specific_Use Int -- 6 bits
     deriving (Show, Eq)

isTP_PID_Bit5_Bits4_0 (TP_PID_Bit5_Bits4_0 _ _) = True
isTP_PID_Bit5_Bits4_0 _ = False

isTP_PID_Bits5_0_ (TP_PID_Bits5_0_ _) = True
isTP_PID_Bits5_0_ _ = False

isTP_PID_Bits5_0_Reserved (TP_PID_Bits5_0_Reserved _) = True
isTP_PID_Bits5_0_Reserved _ = False

isTP_PID_Bits5_0_SC_Specific_Use (TP_PID_Bits5_0_SC_Specific_Use _) = True
isTP_PID_Bits5_0_SC_Specific_Use _ = False


instance BitRep TP_PID_Bits5_0 TP_PID_Bits7_6 where
   encode TP_PID_Bits7_6_00 (TP_PID_Bit5_Bits4_0 tp_pid_bit5 tp_pid_bits4_0)
      = encode TP_PID_Bits7_6_00 tp_pid_bit5
        ++ encode (TP_PID_Bits7_6_00, tp_pid_bit5) tp_pid_bits4_0

   encode TP_PID_Bits7_6_01 (TP_PID_Bits5_0_ tp_pid_bits5_0_)
      = encode TP_PID_Bits7_6_01 tp_pid_bits5_0_

   encode TP_PID_Bits7_6_Reserved (TP_PID_Bits5_0_Reserved i)
      = if 0 <= i && i <= 2^6 - 1
        then drop 2 (intToBits8 i)
        else error ("[encode] TP_PID_Bits7_6_Reserved : " ++ show i)
   encode TP_PID_Bits7_6_SC_specific_use (TP_PID_Bits5_0_SC_Specific_Use i)
      = if 0 <= i && i <= 2^6 - 1
        then drop 2 (intToBits8 i)
        else error ("[encode] TP_PID_Bits5_0_SC_Specific_Use : " ++ show i)

   decode TP_PID_Bits7_6_00 bits
      = let (tp_pid_bit5,bits1) = decode TP_PID_Bits7_6_00 bits
            (tp_pid_bits4_0,bits2)
                = decode (TP_PID_Bits7_6_00, tp_pid_bit5) bits1
        in
            (TP_PID_Bit5_Bits4_0 tp_pid_bit5 tp_pid_bits4_0, bits2)

   decode TP_PID_Bits7_6_01 bits
      = let (tp_pid_bits5_0_ ,bits') = decode TP_PID_Bits7_6_01 bits
        in (TP_PID_Bits5_0_ tp_pid_bits5_0_, bits')

   decode TP_PID_Bits7_6_Reserved (b5:b4:b3:b2:b1:b0:bits)
      = (TP_PID_Bits5_0_Reserved (bits8ToInt [0,0,b5,b4,b3,b2,b1,b0]), bits)
   decode TP_PID_Bits7_6_Reserved bits
      = error ("[decode] TP_PID_Bits7_6_Reserved : " ++ show bits)

   decode TP_PID_Bits7_6_SC_specific_use (b5:b4:b3:b2:b1:b0:bits)
      = (TP_PID_Bits5_0_SC_Specific_Use (bits8ToInt [0,0,b5,b4,b3,b2,b1,b0]), bits)
   decode TP_PID_Bits7_6_SC_specific_use bits
      = error ("[decode] TP_PID_Bits7_6_SC_specific_use : " ++ show bits)

instance Variant TP_PID_Bits5_0 where
   valid = oneof [ do tp_pid_bit5 <- valid
                      tp_pid_bit4_0 <- valid `suchThat` 
                        (\tp_pid_bit4_0 -> 
                            isTP_PID_Bit5_Telematic_interworking tp_pid_bit5
                            && isTP_PID_Bits4_0_STSP tp_pid_bit4_0 == False
                         || isTP_PID_Bit5_Sme_to_sme_protocol tp_pid_bit5
                            && isTP_PID_Bits4_0_STSP tp_pid_bit4_0 == True )
                      return (TP_PID_Bit5_Bits4_0 tp_pid_bit5 tp_pid_bit4_0),
                   liftM  TP_PID_Bits5_0_ valid,
                   liftM  TP_PID_Bits5_0_Reserved (choose (0,2^6 - 1)),
                   liftM  TP_PID_Bits5_0_SC_Specific_Use (choose (0,2^6 - 1))
                 ]
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Protocol-Identifier bit 5 when Bit7 and Bit6 are 00
--------------------------------------------------------------------------------
data TP_PID_Bit5 =
     TP_PID_Bit5_Sme_to_sme_protocol     {- 0 -}
   | TP_PID_Bit5_Telematic_interworking  {- 1 -}
     deriving (Show, Eq)

isTP_PID_Bit5_Sme_to_sme_protocol TP_PID_Bit5_Sme_to_sme_protocol = True
isTP_PID_Bit5_Sme_to_sme_protocol _ = False

isTP_PID_Bit5_Telematic_interworking TP_PID_Bit5_Telematic_interworking = True
isTP_PID_Bit5_Telematic_interworking _ = False

instance BitRep TP_PID_Bit5 TP_PID_Bits7_6 where
   encode TP_PID_Bits7_6_00 TP_PID_Bit5_Sme_to_sme_protocol = [0]
   encode TP_PID_Bits7_6_00 TP_PID_Bit5_Telematic_interworking = [1]
   encode tp_pid_bits7_6 tp_pid_bit5
      = error ("[encode] TP_PID_Bit5 : " ++ show tp_pid_bits7_6 ++ ", " ++ show tp_pid_bit5)

   decode TP_PID_Bits7_6_00 (0:bits) = (TP_PID_Bit5_Sme_to_sme_protocol, bits)
   decode TP_PID_Bits7_6_00 (1:bits) = (TP_PID_Bit5_Telematic_interworking, bits)
   decode tp_pid_bits7_6 bits
      = error ("[decode] TP_PID_Bit5 : " ++ show tp_pid_bits7_6 ++ ", " ++ show bits)

instance Variant TP_PID_Bit5 where
   valid = elements [ TP_PID_Bit5_Sme_to_sme_protocol,
                      TP_PID_Bit5_Telematic_interworking ]
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Protocol-Identifier 4 to 0 bits when Bit7 and Bit6 are 00
--------------------------------------------------------------------------------
data TP_PID_Bits4_0 =
     TP_PID_Bits4_0_Implicit                 {- 00000 -}
   | TP_PID_Bits4_0_Telex                    {- 00001 -}
   | TP_PID_Bits4_0_Group3_telefax           {- 00010 -}
   | TP_PID_Bits4_0_Group4_telefax           {- 00011 -}
   | TP_PID_Bits4_0_Voice_telephoney         {- 00100 -}
   | TP_PID_Bits4_0_ERMES                    {- 00101 -}
   | TP_PID_Bits4_0_National_paging_system   {- 00110 -}
   | TP_PID_Bits4_0_Videotex                 {- 00111 -}
   | TP_PID_Bits4_0_Teletex                  {- 01000 -}
   | TP_PID_Bits4_0_Teletex_in_PSPDN         {- 01001 -}
   | TP_PID_Bits4_0_Teletex_in_CSPDN         {- 01010 -}
   | TP_PID_Bits4_0_Teletex_in_analog_PSTN   {- 01011 -}
   | TP_PID_Bits4_0_Teletex_in_digital_ISDN  {- 01100 -}
   | TP_PID_Bits4_0_UCI                      {- 01101 -}
   | TP_PID_Bits4_0_Reserved1                {- 01110 -}
   | TP_PID_Bits4_0_Reserved2                {- 01111 -}
   | TP_PID_Bits4_0_Msg_handling_facility    {- 10000 -}
   | TP_PID_Bits4_0_X400_msg_handling_system {- 10001 -}
   | TP_PID_Bits4_0_Internet_email           {- 10010 -}
   | TP_PID_Bits4_0_Reserved3                {- 10011 -}
   | TP_PID_Bits4_0_Reserved4                {- 10100 -}
   | TP_PID_Bits4_0_Reserved5                {- 10101 -}
   | TP_PID_Bits4_0_Reserved6                {- 10110 -}
   | TP_PID_Bits4_0_Reserved7                {- 10111 -}
   | TP_PID_Bits4_0_Specific_to_SC1          {- 11000 -}
   | TP_PID_Bits4_0_Specific_to_SC2          {- 11001 -}
   | TP_PID_Bits4_0_Specific_to_SC3          {- 11010 -}
   | TP_PID_Bits4_0_Specific_to_SC4          {- 11011 -}
   | TP_PID_Bits4_0_Specific_to_SC5          {- 11100 -}
   | TP_PID_Bits4_0_Specific_to_SC6          {- 11101 -}
   | TP_PID_Bits4_0_Specific_to_SC7          {- 11110 -}
   | TP_PID_Bits4_0_Gsm_UMTS_mobile_station  {- 11111 -}

   | TP_PID_Bits4_0_STSP Int  -- This is for SME-TO-SME-Protocol
     deriving (Show, Eq)

isTP_PID_Bits4_0_STSP (TP_PID_Bits4_0_STSP i) = True
isTP_PID_Bits4_0_STSP _  = False

instance BitRep TP_PID_Bits4_0 (TP_PID_Bits7_6, TP_PID_Bit5) where
     encode (TP_PID_Bits7_6_00, TP_PID_Bit5_Sme_to_sme_protocol) = 
         (\x -> case x of
                 TP_PID_Bits4_0_STSP i
                   -> if 0 <= i && i <= 2^5 - 1 then drop 3 (intToBits8 i)
                      else error ("[encode] TP_PID_Bits7_6_00, TP_PID_Bit5_Sme_to_sme_protocol : " ++ show x)
                 _ -> error ("[encode] TP_PID_Bits7_6_00, TP_PID_Bit5_Sme_to_sme_protocol : " ++ show x))

     encode (TP_PID_Bits7_6_00, TP_PID_Bit5_Telematic_interworking)=
         (\x -> case x of 
                 TP_PID_Bits4_0_Implicit -> [0,0,0,0,0]
                 TP_PID_Bits4_0_Telex -> [0,0,0,0,1]
                 TP_PID_Bits4_0_Group3_telefax -> [0,0,0,1,0]
                 TP_PID_Bits4_0_Group4_telefax -> [0,0,0,1,1]
                 TP_PID_Bits4_0_Voice_telephoney -> [0,0,1,0,0]
                 TP_PID_Bits4_0_ERMES -> [0,0,1,0,1]
                 TP_PID_Bits4_0_National_paging_system -> [0,0,1,1,0]
                 TP_PID_Bits4_0_Videotex -> [0,0,1,1,1]
                 TP_PID_Bits4_0_Teletex -> [0,1,0,0,0]
                 TP_PID_Bits4_0_Teletex_in_PSPDN -> [0,1,0,0,1]
                 TP_PID_Bits4_0_Teletex_in_CSPDN -> [0,1,0,1,0]
                 TP_PID_Bits4_0_Teletex_in_analog_PSTN -> [0,1,0,1,1]
                 TP_PID_Bits4_0_Teletex_in_digital_ISDN -> [0,1,1,0,0]
                 TP_PID_Bits4_0_UCI -> [0,1,1,0,1]
                 TP_PID_Bits4_0_Reserved1 -> [0,1,1,1,0]
                 TP_PID_Bits4_0_Reserved2 -> [0,1,1,1,1]
                 TP_PID_Bits4_0_Msg_handling_facility -> [1,0,0,0,0]
                 TP_PID_Bits4_0_X400_msg_handling_system -> [1,0,0,0,1]
                 TP_PID_Bits4_0_Internet_email -> [1,0,0,1,0]
                 TP_PID_Bits4_0_Reserved3 -> [1,0,0,1,1]
                 TP_PID_Bits4_0_Reserved4 -> [1,0,1,0,0]
                 TP_PID_Bits4_0_Reserved5 -> [1,0,1,0,1]
                 TP_PID_Bits4_0_Reserved6 -> [1,0,1,1,0]
                 TP_PID_Bits4_0_Reserved7 -> [1,0,1,1,1]
                 TP_PID_Bits4_0_Specific_to_SC1 -> [1,1,0,0,0]
                 TP_PID_Bits4_0_Specific_to_SC2 -> [1,1,0,0,1]
                 TP_PID_Bits4_0_Specific_to_SC3 -> [1,1,0,1,0]
                 TP_PID_Bits4_0_Specific_to_SC4 -> [1,1,0,1,1]
                 TP_PID_Bits4_0_Specific_to_SC5 -> [1,1,1,0,0]
                 TP_PID_Bits4_0_Specific_to_SC6 -> [1,1,1,0,1]
                 TP_PID_Bits4_0_Specific_to_SC7 -> [1,1,1,1,0]
                 TP_PID_Bits4_0_Gsm_UMTS_mobile_station -> [1,1,1,1,1]  )

     encode cond = \bit4_0 -> error ("[encode] TP_PID_Bit4_0 : " ++ "cond=" ++ show cond ++ ", bit4_0=" ++ show bit4_0)


     decode (TP_PID_Bits7_6_00, TP_PID_Bit5_Sme_to_sme_protocol)
         (b4:b3:b2:b1:b0:bits) = (TP_PID_Bits4_0_STSP
                (bits8ToInt [0,0,0,b4,b3,b2,b1,b0]), bits)

     decode (TP_PID_Bits7_6_00, TP_PID_Bit5_Telematic_interworking) x = 
        case x of 
           (0:0:0:0:0:bits) -> (TP_PID_Bits4_0_Implicit, bits)
           (0:0:0:0:1:bits) -> (TP_PID_Bits4_0_Telex, bits)
           (0:0:0:1:0:bits) -> (TP_PID_Bits4_0_Group3_telefax, bits)
           (0:0:0:1:1:bits) -> (TP_PID_Bits4_0_Group4_telefax, bits)
           (0:0:1:0:0:bits) -> (TP_PID_Bits4_0_Voice_telephoney, bits)
           (0:0:1:0:1:bits) -> (TP_PID_Bits4_0_ERMES, bits)
           (0:0:1:1:0:bits) -> (TP_PID_Bits4_0_National_paging_system, bits)
           (0:0:1:1:1:bits) -> (TP_PID_Bits4_0_Videotex, bits)
           (0:1:0:0:0:bits) -> (TP_PID_Bits4_0_Teletex, bits)
           (0:1:0:0:1:bits) -> (TP_PID_Bits4_0_Teletex_in_PSPDN, bits)
           (0:1:0:1:0:bits) -> (TP_PID_Bits4_0_Teletex_in_CSPDN, bits)
           (0:1:0:1:1:bits) -> (TP_PID_Bits4_0_Teletex_in_analog_PSTN, bits)
           (0:1:1:0:0:bits) -> (TP_PID_Bits4_0_Teletex_in_digital_ISDN, bits)
           (0:1:1:0:1:bits) -> (TP_PID_Bits4_0_UCI, bits)
           (0:1:1:1:0:bits) -> (TP_PID_Bits4_0_Reserved1, bits)
           (0:1:1:1:1:bits) -> (TP_PID_Bits4_0_Reserved2, bits)
           (1:0:0:0:0:bits) -> (TP_PID_Bits4_0_Msg_handling_facility, bits)
           (1:0:0:0:1:bits) -> (TP_PID_Bits4_0_X400_msg_handling_system, bits)
           (1:0:0:1:0:bits) -> (TP_PID_Bits4_0_Internet_email, bits)
           (1:0:0:1:1:bits) -> (TP_PID_Bits4_0_Reserved3, bits)
           (1:0:1:0:0:bits) -> (TP_PID_Bits4_0_Reserved4, bits)
           (1:0:1:0:1:bits) -> (TP_PID_Bits4_0_Reserved5, bits)
           (1:0:1:1:0:bits) -> (TP_PID_Bits4_0_Reserved6, bits)
           (1:0:1:1:1:bits) -> (TP_PID_Bits4_0_Reserved7, bits)
           (1:1:0:0:0:bits) -> (TP_PID_Bits4_0_Specific_to_SC1, bits)
           (1:1:0:0:1:bits) -> (TP_PID_Bits4_0_Specific_to_SC2, bits)
           (1:1:0:1:0:bits) -> (TP_PID_Bits4_0_Specific_to_SC3, bits)
           (1:1:0:1:1:bits) -> (TP_PID_Bits4_0_Specific_to_SC4, bits)
           (1:1:1:0:0:bits) -> (TP_PID_Bits4_0_Specific_to_SC5, bits)
           (1:1:1:0:1:bits) -> (TP_PID_Bits4_0_Specific_to_SC6, bits)
           (1:1:1:1:0:bits) -> (TP_PID_Bits4_0_Specific_to_SC7, bits)
           (1:1:1:1:1:bits) -> (TP_PID_Bits4_0_Gsm_UMTS_mobile_station, bits) 
     decode cond bits = error ("[decode] TP_PID_Bit5 : cond=" ++ show cond ++ " bits=" ++ show bits)

instance Variant TP_PID_Bits4_0 where
   valid = oneof ( map return [
            TP_PID_Bits4_0_Implicit,
            TP_PID_Bits4_0_Telex,
            TP_PID_Bits4_0_Group3_telefax,
            TP_PID_Bits4_0_Group4_telefax,
            TP_PID_Bits4_0_Voice_telephoney,
            TP_PID_Bits4_0_ERMES,
            TP_PID_Bits4_0_National_paging_system,
            TP_PID_Bits4_0_Videotex,
            TP_PID_Bits4_0_Teletex,
            TP_PID_Bits4_0_Teletex_in_PSPDN,
            TP_PID_Bits4_0_Teletex_in_CSPDN,
            TP_PID_Bits4_0_Teletex_in_analog_PSTN,
            TP_PID_Bits4_0_Teletex_in_digital_ISDN,
            TP_PID_Bits4_0_UCI,
            TP_PID_Bits4_0_Reserved1,
            TP_PID_Bits4_0_Reserved2,
            TP_PID_Bits4_0_Msg_handling_facility,
            TP_PID_Bits4_0_X400_msg_handling_system,
            TP_PID_Bits4_0_Internet_email,
            TP_PID_Bits4_0_Reserved3,
            TP_PID_Bits4_0_Reserved4,
            TP_PID_Bits4_0_Reserved5,
            TP_PID_Bits4_0_Reserved6,
            TP_PID_Bits4_0_Reserved7,
            TP_PID_Bits4_0_Specific_to_SC1,
            TP_PID_Bits4_0_Specific_to_SC2,
            TP_PID_Bits4_0_Specific_to_SC3,
            TP_PID_Bits4_0_Specific_to_SC4,
            TP_PID_Bits4_0_Specific_to_SC5,
            TP_PID_Bits4_0_Specific_to_SC6,
            TP_PID_Bits4_0_Specific_to_SC7,
            TP_PID_Bits4_0_Gsm_UMTS_mobile_station ] ++

            [ liftM TP_PID_Bits4_0_STSP (choose (0,2^5-1)) ] )

   invalid = valid

--------------------------------------------------------------------------------
-- TP-Protocol-Identifier 5 to 0 bits when Bit7 and Bit6 are 01
--------------------------------------------------------------------------------
data TP_PID_Bits5_0_ =
     TP_PID_Bits5_0_Short_message_type0              {- 000000 -}
   | TP_PID_Bits5_0_Replace_short_message_type1      {- 000001 -}
   | TP_PID_Bits5_0_Replace_short_message_type2      {- 000010 -}
   | TP_PID_Bits5_0_Replace_short_message_type3      {- 000011 -}
   | TP_PID_Bits5_0_Replace_short_message_type4      {- 000100 -}
   | TP_PID_Bits5_0_Replace_short_message_type5      {- 000101 -}
   | TP_PID_Bits5_0_Replace_short_message_type6      {- 000110 -}
   | TP_PID_Bits5_0_Replace_short_message_type7      {- 000111 -}
   | TP_PID_Bits5_0_Reserved001000_011101 Int        {- 001000 ~ 011101 -}
   | TP_PID_Bits5_0_Enhanced_message_service         {- 011110 -}
   | TP_PID_Bits5_0_Return_call_message              {- 011111 -}
   | TP_PID_Bits5_0_Reserved100000_111011 Int        {- 100000 ~ 111011 -}
   | TP_PID_Bits5_0_Ansi_136_R_data                  {- 111100 -}
   | TP_PID_Bits5_0_ME_data_download                 {- 111101 -}
   | TP_PID_Bits5_0_ME_depersonalized_short_message  {- 111110 -}
   | TP_PID_Bits5_0_U_SIM_data_download              {- 111111 -}
     deriving (Show, Eq)

instance BitRep TP_PID_Bits5_0_ TP_PID_Bits7_6 where
   encode TP_PID_Bits7_6_01 =
      (\x -> case x of 
                TP_PID_Bits5_0_Short_message_type0             -> [0,0,0,0,0,0]
                TP_PID_Bits5_0_Replace_short_message_type1     -> [0,0,0,0,0,1]
                TP_PID_Bits5_0_Replace_short_message_type2     -> [0,0,0,0,1,0]
                TP_PID_Bits5_0_Replace_short_message_type3     -> [0,0,0,0,1,1]
                TP_PID_Bits5_0_Replace_short_message_type4     -> [0,0,0,1,0,0]
                TP_PID_Bits5_0_Replace_short_message_type5     -> [0,0,0,1,0,1]
                TP_PID_Bits5_0_Replace_short_message_type6     -> [0,0,0,1,1,0]
                TP_PID_Bits5_0_Replace_short_message_type7     -> [0,0,0,1,1,1]
                TP_PID_Bits5_0_Reserved001000_011101 i         ->
                  if bits8ToInt [0,0,0,0,1,0,0,0] <= i && i <= bits8ToInt [0,0,0,1,1,1,0,1] 
                  then drop 2 (intToBits8 i)
                  else error ("[encode] TP_PID: TP_PID_Bits5_0_Reserved001000_011101 " ++ show i)
                TP_PID_Bits5_0_Enhanced_message_service        -> [0,1,1,1,1,0]
                TP_PID_Bits5_0_Return_call_message             -> [0,1,1,1,1,1]
                TP_PID_Bits5_0_Reserved100000_111011 i         ->
                  if bits8ToInt [0,0,1,0,0,0,0,0] <= i && i <= bits8ToInt [0,0,1,1,1,0,1,1] 
                  then drop 2 (intToBits8 i)
                  else error ("[encode] TP_PID: TP_PID_Bits5_0_Reserved100000_111011 " ++ show i)
                TP_PID_Bits5_0_Ansi_136_R_data                 -> [1,1,1,1,0,0]
                TP_PID_Bits5_0_ME_data_download                -> [1,1,1,1,0,1]
                TP_PID_Bits5_0_ME_depersonalized_short_message -> [1,1,1,1,1,0]
                TP_PID_Bits5_0_U_SIM_data_download             -> [1,1,1,1,1,1] )

   decode TP_PID_Bits7_6_01 =
       (\x -> case x of 
                 (0:0:0:0:0:0:bits) -> (TP_PID_Bits5_0_Short_message_type0, bits)
                 (0:0:0:0:0:1:bits) -> (TP_PID_Bits5_0_Replace_short_message_type1, bits)
                 (0:0:0:0:1:0:bits) -> (TP_PID_Bits5_0_Replace_short_message_type2, bits)
                 (0:0:0:0:1:1:bits) -> (TP_PID_Bits5_0_Replace_short_message_type3, bits)
                 (0:0:0:1:0:0:bits) -> (TP_PID_Bits5_0_Replace_short_message_type4, bits)
                 (0:0:0:1:0:1:bits) -> (TP_PID_Bits5_0_Replace_short_message_type5, bits)
                 (0:0:0:1:1:0:bits) -> (TP_PID_Bits5_0_Replace_short_message_type6, bits)
                 (0:0:0:1:1:1:bits) -> (TP_PID_Bits5_0_Replace_short_message_type7, bits)

                 (0:1:1:1:1:0:bits) -> (TP_PID_Bits5_0_Enhanced_message_service, bits)
                 (0:1:1:1:1:1:bits) -> (TP_PID_Bits5_0_Return_call_message, bits)

                 (1:1:1:1:0:0:bits) -> (TP_PID_Bits5_0_Ansi_136_R_data, bits)
                 (1:1:1:1:0:1:bits) -> (TP_PID_Bits5_0_ME_data_download, bits)
                 (1:1:1:1:1:0:bits) -> (TP_PID_Bits5_0_ME_depersonalized_short_message, bits)
                 (1:1:1:1:1:1:bits) -> (TP_PID_Bits5_0_U_SIM_data_download, bits)

                 (b5:b4:b3:b2:b1:b0:bits) ->
                     if bits8ToInt [0,0,0,0,1,0,0,0] <= bits8ToInt ([0,0]++[b5,b4,b3,b2,b1,b0]) &&
                        bits8ToInt ([0,0]++[b5,b4,b3,b2,b1,b0]) <= bits8ToInt [0,0,0,1,1,1,0,1] 
                     then (TP_PID_Bits5_0_Reserved001000_011101 (bits8ToInt ([0,0] ++ [b5,b4,b3,b2,b1,b0])), bits)
                     else if bits8ToInt [0,0,1,0,0,0,0,0] <= bits8ToInt ([0,0]++[b5,b4,b3,b2,b1,b0]) &&
                        bits8ToInt ([0,0]++[b5,b4,b3,b2,b1,b0]) <= bits8ToInt [0,0,1,1,1,0,1,1]
                     then (TP_PID_Bits5_0_Reserved100000_111011 (bits8ToInt ([0,0] ++ [b5,b4,b3,b2,b1,b0])), bits)
                     else error ("[decode] TP_PID_Bits7_6_01 : " ++ show ([b5,b4,b3,b2,b1,b0]++bits)) )

   decode tp_pid_bits7_6 = \bits -> error ("[decode]  : " ++ show tp_pid_bits7_6 ++ show bits)

instance Variant TP_PID_Bits5_0_ where
   valid = oneof [
             elements [
                TP_PID_Bits5_0_Short_message_type0,
                TP_PID_Bits5_0_Replace_short_message_type1,
                TP_PID_Bits5_0_Replace_short_message_type2,
                TP_PID_Bits5_0_Replace_short_message_type3,
                TP_PID_Bits5_0_Replace_short_message_type4,
                TP_PID_Bits5_0_Replace_short_message_type5,
                TP_PID_Bits5_0_Replace_short_message_type6,
                TP_PID_Bits5_0_Replace_short_message_type7 ],

             liftM TP_PID_Bits5_0_Reserved001000_011101
                (choose (2^3, 2^4 + 2^3 + 2^2 + 2^0)),

             elements [
                TP_PID_Bits5_0_Enhanced_message_service,
                TP_PID_Bits5_0_Return_call_message ],

             liftM TP_PID_Bits5_0_Reserved100000_111011
                (choose (2^5, 2^5 + 2^4 + 2^3 + 2^1 + 2^0)),
             
             elements [ 
                TP_PID_Bits5_0_Ansi_136_R_data,
                TP_PID_Bits5_0_ME_data_download,
                TP_PID_Bits5_0_ME_depersonalized_short_message,
                TP_PID_Bits5_0_U_SIM_data_download ]
           ]
   invalid = valid
      

--------------------------------------------------------------------------------
-- TP-Data-Coding-Scheme (TP-DCS)
--------------------------------------------------------------------------------
data TP_DCS =
     TP_DCS_General    -- 00XX
        Bool           -- b5    Uncompressed/Compressed
        Bool           -- b4    No message class/The message class
        Message_Class  -- b1 b0 
        Character_Set  -- b3 b2 

   | TP_DCS_ADG        -- 01XX
        Bool           -- b5    Uncompressed/Compressed
        Bool           -- b4    No message class/The message class
        Message_Class  -- b1 b0 
        Character_Set  -- b3 b2 

   | TP_DCS_Reserved Int -- 1000XXXX ~ 1011XXXX

   | TP_DCS_MWIG_Discard_Msg Bool Indication_Type       -- 1100

   | TP_DCS_MWIG_Store_Msg_GSM7bit Bool Indication_Type -- GSM7bit
   | TP_DCS_MWIG_Store_Msg_UnCompressed_UCS2 Bool Indication_Type  -- UCS2
   | TP_DCS_Data_Coding_Class Bool Message_Class        -- GSM7bit or UCS2
     deriving (Show, Eq)

dcsToCharacterSet (TP_DCS_General b1 b2 msg_class cs) = cs
dcsToCharacterSet (TP_DCS_ADG b1 b2 msg_class cs) = cs
dcsToCharacterSet (TP_DCS_Reserved i) 
   = error ("[dcsToCharacterSet] " ++ show (TP_DCS_Reserved i))
dcsToCharacterSet (TP_DCS_MWIG_Discard_Msg b ind_type) = GSM7Bit
dcsToCharacterSet (TP_DCS_MWIG_Store_Msg_GSM7bit b ind_type) = GSM7Bit
dcsToCharacterSet (TP_DCS_MWIG_Store_Msg_UnCompressed_UCS2 b ind_type) = UCS2_16Bit
dcsToCharacterSet (TP_DCS_Data_Coding_Class False msg_class) = GSM7Bit
dcsToCharacterSet (TP_DCS_Data_Coding_Class True msg_class) = CS_8Bit

dcsToBytesPerChar dcs = 
   case dcsToCharacterSet dcs of
      GSM7Bit -> 1
      CS_8Bit -> 1
      UCS2_16Bit -> 2

instance BitRep TP_DCS a where
   encode _ (TP_DCS_General flag_compressed  flag_msgclass msgclass cs) 
      = let
            b5 = if flag_compressed then 1 else 0
            b4 = if flag_msgclass then 1 else 0
        in  [0,0] ++ [b5,b4] ++ encode () cs ++ encode () msgclass 

   encode _ (TP_DCS_ADG flag_compressed flag_msgclass msgclass cs)
      = let
            b5 = if flag_compressed then 1 else 0
            b4 = if flag_msgclass then 1 else 0
        in  [0,1] ++ [b5,b4] ++ encode () cs ++ encode () msgclass 

   encode _ (TP_DCS_Reserved i)
      | 128 <= i && i <= 128+63 = intToBits8 i
      | otherwise
        = error ("[encode] TP_DCS_Reserved " ++ show i)

   encode _ (TP_DCS_MWIG_Discard_Msg flag_indication indtype)
      = let b3 = if flag_indication then 1 else 0
        in  [1,1,0,0] ++ [b3] ++ [0] ++ encode () indtype

   encode _ (TP_DCS_MWIG_Store_Msg_GSM7bit flag_indication indtype)
      = let b3 = if flag_indication then 1 else 0
        in  [1,1,0,1] ++ [b3] ++ [0] ++ encode () indtype

   encode _ (TP_DCS_MWIG_Store_Msg_UnCompressed_UCS2 flag_indication indtype)
      = let b3 = if flag_indication then 1 else 0
        in  [1,1,1,0] ++ [b3] ++ [0] ++ encode () indtype

   encode _ (TP_DCS_Data_Coding_Class flag_cs msgclass)
      = let b2 = if flag_cs then 1 else 0
        in  [1,1,1,1] ++ [0] ++ [b2] ++ encode () msgclass


   decode _ (0:0:b5:b4:bits)
      = let (cs, bits1) = decode () bits
            (msg_class, bits2) = decode () bits1
        in  (TP_DCS_General (b5==1) (b4==1) msg_class cs, bits2)

   decode _ (0:1:b5:b4:bits)
      = let (cs, bits1) = decode () bits
            (msg_class, bits2) = decode () bits1
        in  (TP_DCS_ADG (b5==1) (b4==1) msg_class cs, bits2)

   decode _ (1:0:b5:b4:b3:b2:b1:b0:bits)
      = (TP_DCS_Reserved (bits8ToInt [0,0,b5,b4,b3,b2,b1,b0]), bits)

   decode _ (1:1:0:0:b3:b2:bits)
      | b2 == 0   = let (ind_type, bits') = decode () bits
                    in  (TP_DCS_MWIG_Discard_Msg (b3==1) ind_type, bits')
      | otherwise = error ("[decode] TP_DCS_MWIG_Discard : "
                              ++ show (1:1:0:0:b3:b2:bits))

   decode _ (1:1:0:1:b3:b2:bits)
      | b2 == 0   = let (ind_type, bits') = decode () bits
                    in  (TP_DCS_MWIG_Store_Msg_GSM7bit (b3==1) ind_type, bits')
      | otherwise = error ("[decode] TP_DCS_MWIG_Store_Msg_GSM7bit : "
                              ++ show (1:1:0:1:b3:b2:bits))

   decode _ (1:1:1:0:b3:b2:bits)
      | b2 == 0   = let (ind_type, bits') = decode () bits
                    in  (TP_DCS_MWIG_Store_Msg_UnCompressed_UCS2 (b3==1) ind_type, bits')
      | otherwise = error ("[decode] (TP_DCS_MWIG_Store_Msg_UnCompressed_UCS2)"
                              ++ show (1:1:1:0:b3:b2:bits))
                           

   decode _ (1:1:1:1:0:b2:bits)
      = let (msg_class, bits') = decode () bits
        in  (TP_DCS_Data_Coding_Class (b2==1) msg_class, bits')

   decode _ bits = error ("[decode] TP_DCS : " ++ show bits)

instance Variant TP_DCS where
   valid = oneof [
              liftM4 TP_DCS_General valid valid valid valid,
              liftM4 TP_DCS_ADG valid valid valid valid,
              -- TBD
              -- liftM TP_DCS_Reserved (choose (2^7, 2^7+2^5+2^4+2^3+2^2+2^1+2^0)),
              liftM2 TP_DCS_MWIG_Discard_Msg valid valid,
              liftM2 TP_DCS_MWIG_Store_Msg_GSM7bit valid valid,
              liftM2 TP_DCS_MWIG_Store_Msg_UnCompressed_UCS2 valid valid,
              liftM2 TP_DCS_Data_Coding_Class valid valid ]
   invalid = valid

--------------------------------------------------------------------------------
-- Message Class
--------------------------------------------------------------------------------
data Message_Class = Class0 | Class1 | Class2 | Class3
     deriving (Show, Eq)

instance BitRep Message_Class a where
   encode _ Class0 = [0,0]
   encode _ Class1 = [0,1]
   encode _ Class2 = [1,0]
   encode _ Class3 = [1,1]

   decode _ (0:0:bits) = (Class0, bits)
   decode _ (0:1:bits) = (Class1, bits)
   decode _ (1:0:bits) = (Class2, bits)
   decode _ (1:1:bits) = (Class3, bits)

instance Variant Message_Class where
   valid = elements [ Class0, Class1, Class2, Class3 ]
   invalid = valid

--------------------------------------------------------------------------------
-- Character Set
--------------------------------------------------------------------------------
data Character_Set = GSM7Bit | CS_8Bit | UCS2_16Bit | CS_Reserved
     deriving (Show, Eq)

instance BitRep Character_Set a where
   encode _ GSM7Bit = [0,0]
   encode _ CS_8Bit = [0,1]
   encode _ UCS2_16Bit = [1,0]
   encode _ CS_Reserved = [1,1]

   decode _ (0:0:bits) = (GSM7Bit, bits)
   decode _ (0:1:bits) = (CS_8Bit, bits)
   decode _ (1:0:bits) = (UCS2_16Bit, bits)
   decode _ (1:1:bits) = (CS_Reserved, bits)

instance Variant Character_Set where
   valid = elements [ GSM7Bit, CS_8Bit, UCS2_16Bit {- TBD , CS_Reserved -} ]
   invalid = valid

--------------------------------------------------------------------------------
-- Indication Type
--------------------------------------------------------------------------------
data Indication_Type = VoicemailMsgWaiting | FaxMsgWaiting | EMailMsgWaiting | OtherMsgWaiting 
     deriving (Show, Eq)

instance BitRep Indication_Type a where
   encode _ VoicemailMsgWaiting = [0,0]
   encode _ FaxMsgWaiting = [0,1]
   encode _ EMailMsgWaiting = [1,0]
   encode _ OtherMsgWaiting = [1,1]

   decode _ (0:0:bits) = (VoicemailMsgWaiting, bits)
   decode _ (0:1:bits) = (FaxMsgWaiting, bits)
   decode _ (1:0:bits) = (EMailMsgWaiting, bits)
   decode _ (1:1:bits) = (OtherMsgWaiting, bits)

instance Variant Indication_Type where
   valid = elements [ VoicemailMsgWaiting, FaxMsgWaiting, EMailMsgWaiting, OtherMsgWaiting ]
   invalid = valid

--------------------------------------------------------------------------------
-- Service Center Timestamp
--------------------------------------------------------------------------------
data TP_SCTS = TP_SCTS Int Int Int -- Year : 0 ~ 99
                                   -- Month : 1 ~ 12
                                   -- Day : 1 ~ 31
                       Int Int Int -- Hour : 0 ~ 23
                                   -- Minute : 0 ~59
                                   -- Second : 0 ~ 59
                       Int         -- Time Zone : -48 ~ 48
     deriving (Show, Eq)

{- Absolute time definition example
   23rd December 01, 9:53:42 AM, GMT +1 hour
   Year      : 0001 0000   0x10
   Month     : 0010 0001   0x21
   Day       : 0011 0010   0x32
   Hour      : 1001 0000   0x90
   Minute    : 0011 0101   0x35
   Second    : 0010 0100   0x24
   Time Zone : 0100 0 000  0x40 
-}

instance BitRep TP_SCTS a where
   encode _ (TP_SCTS year month day hour minute second time_zone)
           = sctsToBit (year, month, day, hour, minute, second, time_zone)
   decode _ bits
           = (TP_SCTS year month day hour minute second time_zone, bits')
               where ((year, month, day, hour, minute, second, time_zone), bits') = sctsToCon bits
 

sctsToBit (year, month, day, hour, minute, second, time_zone)
   |    (0 <= year && year <= 99
     && 1 <= month && month <= 12
     && 1 <= day && day <= 31
     && 0 <= hour && hour <= 23
     && 0 <= minute && minute <= 59
     && 0 <= second && second <= 59
     && -48 <= time_zone && time_zone <= 48)
       = let { y1 = year `div` 10;
               y2 = year `mod` 10; 

               mo1 = month `div` 10;
               mo2 = month `mod` 10; 

               d1 = day `div` 10;
               d2 = day `mod` 10; 

               h1 = hour `div` 10;
               h2 = hour `mod` 10; 

               m1 = minute `div` 10;
               m2 = minute `mod` 10; 

               s1 = second `div` 10;
               s2 = second `mod` 10; 

               t1 = (if time_zone > 0 then time_zone else -time_zone) `div` 10;
               t2 = (if time_zone > 0 then time_zone else -time_zone) `mod` 10;

               signbit = if time_zone > 0 then 0 else 1
             }
         in
             intToBits8 (y2 * 16 + y1)   ++ 
             intToBits8 (mo2 * 16 + mo1) ++ 
             intToBits8 (d2 * 16 + d1)   ++ 
             intToBits8 (h2 * 16 + h1)   ++ 
             intToBits8 (m2 * 16 + m1)   ++ 
             intToBits8 (s2 * 16 + s1)   ++
             intToBits4 t2 ++ [signbit] ++ drop 1 (intToBits4 t1)
   | otherwise
       = error ("[sctsToBit] : "
                  ++ show [year, month, day, hour, minute, second, time_zone])

sctsToCon bits
   | length bits >= 7*8
       = let { y1 = bits4ToInt (take 4 bits);
               y2 = bits4ToInt (drop 4 (take 8 bits));
               year  = y2 * 10 + y1;

               mo1 = bits4ToInt (take 4 (drop 8 bits));
               mo2 = bits4ToInt (drop 4 (take 8 (drop 8 bits)));
               month  = mo2 * 10 + mo1;

               d1 = bits4ToInt (take 4 (drop 16 bits));
               d2 = bits4ToInt (drop 4 (take 8 (drop 16 bits)));
               day  = d2 * 10 + d1;

               h1 = bits4ToInt (take 4 (drop 24 bits));
               h2 = bits4ToInt (drop 4 (take 8 (drop 24 bits)));
               hour  = h2 * 10 + h1;

               m1 = bits4ToInt (take 4 (drop 32 bits));
               m2 = bits4ToInt (drop 4 (take 8 (drop 32 bits)));
               minute  = m2 * 10 + m1;

               s1 = bits4ToInt (take 4 (drop 40 bits));
               s2 = bits4ToInt (drop 4 (take 8 (drop 40 bits)));
               second  = s2 * 10 + s1;

               tz1        = bits4ToInt (take 4 (drop 48 bits));
               (sign:tz2bits) = drop 4 (take 8 (drop 48 bits));
               tz2 = bits4ToInt (0:tz2bits);
               time_zone  = (if sign==0 then 1 else -1) * (tz2 * 10 + tz1);
             }
         in
          (if 0 <= year && year <= 99
               && 1 <= month && month <= 12
               && 1 <= day && day <= 31
               && 0 <= hour && hour <= 23
               && 0 <= minute && minute <= 59
               && 0 <= second && second <= 59
               && -48 <= time_zone && time_zone <= 48
          then          
             ((year, month, day, hour, minute, second, time_zone), drop 56 bits)
          else 
             error ("[sctsToCon] : " ++ show (year, month, day, hour, minute, second, time_zone) ++ ", " ++ show (drop 56 bits))
          )
   | otherwise
       = error ("[sctsToCon] : " ++ show bits ++ ", (length) : " 
                  ++ show (length bits))

instance Variant TP_SCTS where
   valid = do year <- choose (0,99)
              month <- choose (1,12)
              day <- choose (1,31)
              hour <- choose (0,23)
              minute <- choose (0,59)
              second <- choose (0,59)
              timezone <- choose (-48,48)
              return (TP_SCTS year month day hour minute second timezone)
   invalid = valid


--------------------------------------------------------------------------------
-- TP_Validity-Period (TP-VP)
--------------------------------------------------------------------------------
data TP_VP = 
      TP_VP_Relative Int 
    | TP_VP_Absolute Int Int Int Int Int Int Int 
    | TP_VP_Enhanced TP_VP_Enhanced
    {- Where does this come from?   | TP_VP_Reserved -}
     deriving (Show, Eq)

isTP_VP_Relative (TP_VP_Relative _) = True
isTP_VP_Relative _ = False

isTP_VP_Absolute (TP_VP_Absolute _ _ _ _ _ _ _) = True
isTP_VP_Absolute _ = False

isTP_VP_Enhanced (TP_VP_Enhanced _) = True
isTP_VP_Enhanced _ = False

-- isTP_VP_Reserved TP_VP_Reserved = True
-- isTP_VP_Reserved _ = False

instance BitRep TP_VP TP_VPF where
   encode TP_VP_Field_Present_Relative (TP_VP_Relative i)
      = if 0 <= i && i <= 143 then intToBits8 i
        else if 144 <= i && i <= 167 then intToBits8 i
        else if 168 <= i && i <= 196 then intToBits8 i
        else if 197 <= i && i <= 255 then intToBits8 i
        else error ("[encode] TP_VP_Field_Present_Relative :" ++ show i)
   encode TP_VP_Field_Present_Absolute (TP_VP_Absolute i1 i2 i3 i4 i5 i6 i7)
      = sctsToBit (i1,i2,i3,i4,i5,i6,i7)
   encode TP_VP_Field_Present_Enhanced (TP_VP_Enhanced tp_vp_enhanced)
      = encode () tp_vp_enhanced
   encode tp_vpf tp_vp 
      = error ("[encode] TP_VP : tp_vpf="++ show tp_vpf 
                  ++ ", tp_vp=" ++ show tp_vp)

   decode TP_VP_Field_Present_Relative (b7:b6:b5:b4:b3:b2:b1:b0:bits)
      = (TP_VP_Relative (bits8ToInt (b7:b6:b5:b4:b3:b2:b1:b0:[])), bits)

   decode TP_VP_Field_Present_Absolute bits =
       let ((year, month, day, hour, minute, second, time_zone),bits')
               = sctsToCon bits
       in  (TP_VP_Absolute year month day hour minute second time_zone, bits')

   decode TP_VP_Field_Present_Enhanced bits =
       let (tp_vp_enhanced, bits') = decode () bits
       in  (TP_VP_Enhanced tp_vp_enhanced, bits')
   decode tp_vpf bits = error ("[decode] TP_VP : tp_vpf=" ++ show tp_vpf 
       ++ ", bits=" ++ show bits)

getRelativeValidityPeriod i =
   if 0 <= i && i <= 143 then (i + 1) * 5                     -- Minutes
   else if 144 <= i && i <= 167 then 12 * 60 + (i - 143) * 30 -- Minutes
   else if 168 <= i && i <= 196 then (i - 166) * 24 * 60      -- Minutes
   else if 197 <= i && i <= 255 then (i - 192) * 24 * 7 * 60  -- Minutes
   else error ("[getRelativeValidityPeriod] " ++ show i)

instance Variant TP_VP where
   valid = let tp_vp_relative =
                  do i <- choose (0,255)
                     return (TP_VP_Relative i)

               tp_vp_absolute = 
                  do year <- choose (0,99)
                     month <- choose (1,12)
                     day <- choose (1,31)
                     hour <- choose (0,23)
                     minute <- choose (0,59)
                     second <- choose (0,59)
                     time_zone <- choose (-48,48)
                     return (TP_VP_Absolute year month day hour minute second
                                time_zone)

               tp_vp_enhanced = liftM TP_VP_Enhanced valid

--                tp_vp_reserved = elements [ TP_VP_Reserved ]

           in 
               oneof [ tp_vp_relative, tp_vp_absolute, tp_vp_enhanced {- TBD , tp_vp_reserved -} ]
   invalid = valid

--------------------------------------------------------------------------------
-- TP_Validity-Period Enhanced
--------------------------------------------------------------------------------
data TP_VP_Enhanced =
      TP_VP_Enhanced_No_Validity_Period Bool
       {- XXXXX000 0 Octet  -} 
    | TP_VP_Enhanced_Relative_Period Bool Int
       {- XXXXX001 1 Octet  -}
    | TP_VP_Enhanced_Relative_Period_Integer Bool Int     
       {- XXXXX010 2 Octet  -}
    | TP_VP_Enhanced_Relative_Period_HMS Bool Int Int Int 
       {- XXXXX011 3 Octets -}
    | TP_VP_Enhanced_Reserved Int 
     deriving (Show, Eq)
   
instance BitRep TP_VP_Enhanced a where
   encode _ (TP_VP_Enhanced_No_Validity_Period singleshotsm) 
       {- No extension bit -}
      = [0,b6,0,0,0,0,0,0] 
          where b6 = if singleshotsm then 1 else 0

   encode _ (TP_VP_Enhanced_Relative_Period singleshotsm i)
       {- Extension bit -}
      = [1,b6,0,0,0,0,0,1]
        ++ encode TP_VP_Field_Present_Relative (TP_VP_Relative i)
          where b6 = if singleshotsm then 1 else 0

   encode _ (TP_VP_Enhanced_Relative_Period_Integer singleshotsm i)   
       {- Extension bit -}
      = [1,b6,0,0,0,0,1,0] ++  intToBits8 i 
          where b6 = if singleshotsm then 1 else 0

   encode _ (TP_VP_Enhanced_Relative_Period_HMS singleshotsm i1 i2 i3)
       = [1,b6,0,0,0,0,1,1]
         ++ drop 4 (intToBits8 (i1 `div` 10))
         ++ drop 4 (intToBits8 (i1 `mod` 10))
         ++ drop 4 (intToBits8 (i2 `div` 10))
         ++ drop 4 (intToBits8 (i2 `mod` 10))
         ++ drop 4 (intToBits8 (i3 `div` 10))
         ++ drop 4 (intToBits8 (i3 `mod` 10))
          where b6 = if singleshotsm then 1 else 0

   encode _ (TP_VP_Enhanced_Reserved i)
       = case intToBits8 i of
           [b7,b6,b5,b4,b3,b2,b1,b0] -> 
                if b7 == 0 
                   && 4 <= bits8ToInt [0,0,0,0,0,b2,b1,b0]
                   && bits8ToInt [0,0,0,0,0,b2,b1,b0] <= 7
                then 
                   [b7,b6,b5,b4,b3,b2,b1,b0]
                else error ("[encode] TP_VP_Enhanced_Reserved " ++ show i)
           _ -> error ("[encode] TP_VP_Enhanced_Reserved " ++ show i)

   decode _ (0:b:0:0:0:0:0:0:bits)
       = (TP_VP_Enhanced_No_Validity_Period singleshotsm, bits)
          where singleshotsm = if b==1 then True else False

   decode _ (1:b:0:0:0:0:0:1:b7:b6:b5:b4:b3:b2:b1:b0:bits)
       = (TP_VP_Enhanced_Relative_Period singleshotsm
            (bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]), bits)
          where singleshotsm = if b==1 then True else False

   decode _ (1:b:0:0:0:0:1:0:b7:b6:b5:b4:b3:b2:b1:b0:bits)
       = (TP_VP_Enhanced_Relative_Period_Integer singleshotsm
            (bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]), bits)
          where singleshotsm = if b==1 then True else False

   decode _ (1:b:0:0:0:0:1:1:b7:b6:b5:b4:b3:b2:b1:b0:b7':b6':b5':b4':b3':b2':b1':b0':b7'':b6'':b5'':b4'':b3'':b2'':b1'':b0'':bits)
       = (TP_VP_Enhanced_Relative_Period_HMS singleshotsm 
                 (bits8ToInt [0,0,0,0,b7,b6,b5,b4] * 10
                   + bits8ToInt[0,0,0,0,b3,b2,b1,b0])
                 (bits8ToInt [0,0,0,0,b7',b6',b5',b4'] * 10 
                   + bits8ToInt[0,0,0,0,b3',b2',b1',b0'])
                 (bits8ToInt [0,0,0,0,b7'',b6'',b5'',b4''] * 10 
                   + bits8ToInt[0,0,0,0,b3'',b2'',b1'',b0'']), bits)
          where singleshotsm = if b==1 then True else False

   decode _ (b7:b6:b5:b4:b3:b2:b1:b0:bits)
      | b7==0 
        && 4 <= bits8ToInt [0,0,0,0,0,b2,b1,b0]
        && bits8ToInt [0,0,0,0,0,b2,b1,b0] <= 7
          = (TP_VP_Enhanced_Reserved (bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]), bits)
      | otherwise 
          = error ("[decode] TP_VP_Enhanced_... : " ++ show (b7:b6:b5:b4:b3:b2:b1:b0:bits))

   decode _ bits = error ("[decode] TP_VP_Enhanced_... : " ++ show bits)

instance Variant TP_VP_Enhanced where
   valid = let
              tp_vp_enhanced1 = liftM TP_VP_Enhanced_No_Validity_Period valid
              tp_vp_enhanced2 = 
                 do i <- choose (0,255)
                    b <- valid
                    return (TP_VP_Enhanced_Relative_Period b i)
              tp_vp_enhanced3 = 
                 do i <- choose (0,255)
                    b <- valid
                    return (TP_VP_Enhanced_Relative_Period_Integer b i)
              tp_vp_enhanced4 = 
                 do i1 <- choose (0,99)
                    i2 <- choose (0,99)
                    i3 <- choose (0,99)
                    b <- valid
                    return (TP_VP_Enhanced_Relative_Period_HMS b i1 i2 i3)
--               tp_vp_enhanced5 = 
--                  do i <- choose (0,255)
--                     return (TP_VP_Enhanced_Reserved i)
          in
              oneof [ tp_vp_enhanced1, tp_vp_enhanced2, tp_vp_enhanced3, 
                      tp_vp_enhanced4 {- TBD , tp_vp_enhanced5 -} ]
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Discharge-Time (TP-DT)
--------------------------------------------------------------------------------
data TP_DT = TP_DT Int Int Int Int Int Int Int 
     deriving (Show, Eq)

instance BitRep TP_DT () where
   encode _ (TP_DT i1 i2 i3 i4 i5 i6 i7) = sctsToBit (i1,i2,i3,i4,i5,i6,i7)

   decode _ bits = (TP_DT year month day hour minute second time_zone, bits')
          where ((year, month, day, hour, minute, second, time_zone), bits') = sctsToCon bits

instance Variant TP_DT where
   valid = do year <- choose (0,99)
              month <- choose (1,12)
              day <- choose (1,31)
              hour <- choose (0,23)
              minute <- choose (0,59)
              second <- choose (0,59)
              time_zone <- choose (-48,48)
              return (TP_DT year month day hour minute second time_zone)
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Recipient-Address (TP-RA)
--------------------------------------------------------------------------------
data TP_RA = TP_RA AddrFields
     deriving (Show, Eq)

instance BitRep TP_RA () where
   encode _ (TP_RA addrfields) = encode () addrfields

   decode _ bits = let (ra, bits') = decode () bits
                  in  (TP_RA ra, bits')

instance Variant TP_RA where
   valid = liftM TP_RA valid
   invalid = valid

--------------------------------------------------------------------------------
-- TP_Stauts (TP-ST)
--------------------------------------------------------------------------------
data TP_ST =
     TP_ST_Short_msg_received_by_the_SME                    -- 00000000
   | TP_ST_Short_msg_failed_to_confirm_delivery             -- 00000001
   | TP_ST_Short_msg_replaced_by_the_SC                     -- 00000010
   | TP_ST_Short_msg_transaction_complted_Reserved Int      -- 00000011 ~ 00001111

   {- Temporary error, SC still trying to transfer SM -}
   | TP_ST_Temporary_error_Congestion                       -- 00100000
   | TP_ST_Temporary_error_SME_busy                         -- 00100001
   | TP_ST_Temporary_error_No_response_from_SME             -- 00100010
   | TP_ST_Temporary_error_Service_rejected                 -- 00100011
   | TP_ST_Temporary_error_Quality_of_service_unavailable   -- 00100100
   | TP_ST_Temporary_error_Error_in_SME                     -- 00100101
   | TP_ST_Temporary_error_Reserved Int                     -- 00100110 ~ 00101111
   | TP_ST_Temporary_error_Values_specific_to_SC Int        -- 00110000 ~ 00111111

   | TP_ST_Permanent_error_Remote_procedure_error           -- 01000000
   | TP_ST_Permanent_error_Incompatible_destination         -- 01000001
   | TP_ST_Permanent_error_Connection_rejected_by_SME       -- 01000010
   | TP_ST_Permanent_error_Not_obtaineable                  -- 01000011
   | TP_ST_Permanent_error_Quality_of_service_unavailable   -- 01000100
   | TP_ST_Permanent_error_No_interworking_available        -- 01000101
   | TP_ST_Permanent_error_SM_validity_peirod_expired       -- 01000110
   | TP_ST_Permanent_error_SM_deleted_by_originating_SME    -- 01000111
   | TP_ST_Permanent_error_SM_deleted_by_SC_administration  -- 01001000
   | TP_ST_Permanent_error_SM_not_present                   -- 01001001
   | TP_ST_Permanent_error_Reserved Int                     -- 01001010 ~ 01001111
   | TP_ST_Permanent_error_Values_specific_to_SC Int        -- 01010000 ~ 01011111

   {- Temporary error, SC is not making any more trnasfer attempts  -}
   | TP_ST_Temporary_failure_Congenstion                    -- 01100000
   | TP_ST_Temporary_failure_SME_busy                       -- 01100001
   | TP_ST_Temporary_failure_No_response_from_SME           -- 01100010
   | TP_ST_Temporary_failure_Service_rejected               -- 01100011
   | TP_ST_Temporary_failure_Quality_of_service_unavailable -- 01100100
   | TP_ST_Temporary_failure_Error_in_SME                   -- 01100101
   | TP_ST_Temporary_failure_Reserved1 Int                  -- 01100110 ~ 01101001
   | TP_ST_Temporary_failure_Reserved2 Int                  -- 01101010 ~ 01101111
   | TP_ST_Temporary_failure_Values_specific_to_SC Int      -- 01110000 ~ 01111111

   | TP_ST_Reserved Int                                     -- 1XXXXXXX
     deriving (Show, Eq)


instance BitRep TP_ST a where
   encode _ TP_ST_Short_msg_received_by_the_SME
      = [0,0,0,0,0,0,0,0]
   encode _ TP_ST_Short_msg_failed_to_confirm_delivery
      = [0,0,0,0,0,0,0,1]
   encode _ TP_ST_Short_msg_replaced_by_the_SC                     
      = [0,0,0,0,0,0,1,0]
   encode _ (TP_ST_Short_msg_transaction_complted_Reserved i)
      --  0000 0011 ~ 0000 1111
      | 3 <= i && i <= 15 = [0,0,0,0] ++ intToBits4 i
      | otherwise = error ("[encode] TP_ST_Short_msg_transaction_completed_Reserved " ++ show i)

   encode _ TP_ST_Temporary_error_Congestion
      = [0,0,1,0,0,0,0,0]
   encode _ TP_ST_Temporary_error_SME_busy                         
      = [0,0,1,0,0,0,0,1]
   encode _ TP_ST_Temporary_error_No_response_from_SME             
      = [0,0,1,0,0,0,1,0]
   encode _ TP_ST_Temporary_error_Service_rejected                 
      = [0,0,1,0,0,0,1,1]
   encode _ TP_ST_Temporary_error_Quality_of_service_unavailable   
      = [0,0,1,0,0,1,0,0]
   encode _ TP_ST_Temporary_error_Error_in_SME                     
      = [0,0,1,0,0,1,0,1]
   encode _ (TP_ST_Temporary_error_Reserved i)
      -- 0010 0110 ~ 0010 1111
      | 6 <= i && i <= 15 = [0,0,1,0] ++ intToBits4 i
      | otherwise = error ("[encode] TP_ST_Temporary_error_Reserved " ++ show i)
   encode _ (TP_ST_Temporary_error_Values_specific_to_SC i)        
      -- 0011 0000 ~ 0011 1111
      | 0 <= i && i <= 15 = [0,0,1,1] ++ intToBits4 i
      | otherwise = error ("[encode] TP_ST_Temporary_error_Values_specific_to_SC " ++ show i)

   encode _ TP_ST_Permanent_error_Remote_procedure_error           
      = [0,1,0,0,0,0,0,0]
   encode _ TP_ST_Permanent_error_Incompatible_destination         
      = [0,1,0,0,0,0,0,1]
   encode _ TP_ST_Permanent_error_Connection_rejected_by_SME       
      = [0,1,0,0,0,0,1,0]
   encode _ TP_ST_Permanent_error_Not_obtaineable                  
      = [0,1,0,0,0,0,1,1]
   encode _ TP_ST_Permanent_error_Quality_of_service_unavailable   
      = [0,1,0,0,0,1,0,0]
   encode _ TP_ST_Permanent_error_No_interworking_available        
      = [0,1,0,0,0,1,0,1]
   encode _ TP_ST_Permanent_error_SM_validity_peirod_expired       
      = [0,1,0,0,0,1,1,0]
   encode _ TP_ST_Permanent_error_SM_deleted_by_originating_SME    
      = [0,1,0,0,0,1,1,1]
   encode _ TP_ST_Permanent_error_SM_deleted_by_SC_administration  
      = [0,1,0,0,1,0,0,0]
   encode _ TP_ST_Permanent_error_SM_not_present                   
      = [0,1,0,0,1,0,0,1]
   encode _ (TP_ST_Permanent_error_Reserved i)                     
      -- 0100 1010 ~ 0100 1111
      | 10 <= i && i <= 15 = [0,1,0,0] ++ intToBits4 i
      | otherwise = error ("[encode] TP_ST_Permanent_error_Reserved " ++ show i)
   encode _ (TP_ST_Permanent_error_Values_specific_to_SC i)
      -- 0101 0000 ~ 0101 1111
      | 0 <= i && i <= 15 = [0,1,0,1] ++ intToBits4 i
      | otherwise = error ("[encode] TP_ST_Permanent_error_Values_specific_to_SC " ++ show i)

   encode _ TP_ST_Temporary_failure_Congenstion                    
      = [0,1,1,0,0,0,0,0]
   encode _ TP_ST_Temporary_failure_SME_busy                       
      = [0,1,1,0,0,0,0,1]
   encode _ TP_ST_Temporary_failure_No_response_from_SME           
      = [0,1,1,0,0,0,1,0]
   encode _ TP_ST_Temporary_failure_Service_rejected               
      = [0,1,1,0,0,0,1,1]
   encode _ TP_ST_Temporary_failure_Quality_of_service_unavailable 
      = [0,1,1,0,0,1,0,0]
   encode _ TP_ST_Temporary_failure_Error_in_SME                   
      = [0,1,1,0,0,1,0,1]
   encode _ (TP_ST_Temporary_failure_Reserved1 i)                  
      -- 0110 0110 ~ 0110 1001
      | 6 <= i && i <= 9 = [0,1,1,0] ++ intToBits4 i
      | otherwise = error ("[encode] TP_ST_Temporary_failure_Reserved1 "
                                 ++ show i)
   encode _ (TP_ST_Temporary_failure_Reserved2 i)                  
      -- 0110 1010 ~ 0110 1111
      | 10 <= i && i <= 15 = [0,1,1,0] ++ intToBits4 i
      | otherwise = error ("[encode] TP_ST_Temporary_failure_Reserved2 "
                                 ++ show i)
   encode _ (TP_ST_Temporary_failure_Values_specific_to_SC i)      
      -- 0111 0000 ~ 0111 1111
      | 0 <= i && i <= 15 = [0,1,1,1] ++ intToBits4 i
      | otherwise = error ("[encode] TP_ST_Temporary_failure_Values_specific_to_SC " ++ show i)

   encode _ (TP_ST_Reserved i)                                     
      -- 1XXXXXXX
      | 0 <= i && i <= 127 = [1] ++ drop 1 (intToBits8 i)
      | otherwise = error ("[encode] TP_ST_Reserved " ++ show i)


   decode _ (0:0:0:0:0:0:0:0:bits) = (TP_ST_Short_msg_received_by_the_SME, bits)
   decode _ (0:0:0:0:0:0:0:1:bits) 
      = (TP_ST_Short_msg_failed_to_confirm_delivery, bits)
   decode _ (0:0:0:0:0:0:1:0:bits) 
      = (TP_ST_Short_msg_replaced_by_the_SC, bits)
   decode _ (0:0:0:0:b3:b2:b1:b0:bits) 
      --  0000 0011 ~ 0000 1111
      = (TP_ST_Short_msg_transaction_complted_Reserved
            (bits4ToInt [b3,b2,b1,b0]), bits)  

   decode _ (0:0:1:0:0:0:0:0:bits) = (TP_ST_Temporary_error_Congestion, bits)
   decode _ (0:0:1:0:0:0:0:1:bits) = (TP_ST_Temporary_error_SME_busy, bits)
   decode _ (0:0:1:0:0:0:1:0:bits) 
      = (TP_ST_Temporary_error_No_response_from_SME, bits)
   decode _ (0:0:1:0:0:0:1:1:bits) 
      = (TP_ST_Temporary_error_Service_rejected, bits)
   decode _ (0:0:1:0:0:1:0:0:bits) 
      = (TP_ST_Temporary_error_Quality_of_service_unavailable, bits)
   decode _ (0:0:1:0:0:1:0:1:bits) = (TP_ST_Temporary_error_Error_in_SME, bits)
   decode _ (0:0:1:0:b3:b2:b1:b0:bits)                     
      -- 0010 0110 ~ 0010 1111
      | 6 <= (bits4ToInt [b3,b2,b1,b0]) && (bits4ToInt [b3,b2,b1,b0]) <= 15
          = (TP_ST_Temporary_error_Reserved (bits4ToInt [b3,b2,b1,b0]), bits)
      | otherwise = error ("[decode] TP_ST_Temporary_error_Reserved "
                              ++ show [b3,b2,b1,b0])
   decode _ (0:0:1:1:b3:b2:b1:b0:bits)
      -- 0011 0000 ~ 0011 1111
      = (TP_ST_Temporary_error_Values_specific_to_SC
            (bits4ToInt [b3,b2,b1,b0]), bits)

   decode _ (0:1:0:0:0:0:0:0:bits) 
      = (TP_ST_Permanent_error_Remote_procedure_error, bits)
   decode _ (0:1:0:0:0:0:0:1:bits) 
      = (TP_ST_Permanent_error_Incompatible_destination, bits)
   decode _ (0:1:0:0:0:0:1:0:bits) 
      = (TP_ST_Permanent_error_Connection_rejected_by_SME, bits)
   decode _ (0:1:0:0:0:0:1:1:bits) 
      = (TP_ST_Permanent_error_Not_obtaineable, bits)
   decode _ (0:1:0:0:0:1:0:0:bits) 
      = (TP_ST_Permanent_error_Quality_of_service_unavailable, bits)
   decode _ (0:1:0:0:0:1:0:1:bits) 
      = (TP_ST_Permanent_error_No_interworking_available, bits)
   decode _ (0:1:0:0:0:1:1:0:bits) 
      = (TP_ST_Permanent_error_SM_validity_peirod_expired, bits)
   decode _ (0:1:0:0:0:1:1:1:bits) 
      = (TP_ST_Permanent_error_SM_deleted_by_originating_SME, bits)
   decode _ (0:1:0:0:1:0:0:0:bits) 
      = (TP_ST_Permanent_error_SM_deleted_by_SC_administration, bits)
   decode _ (0:1:0:0:1:0:0:1:bits) 
      = (TP_ST_Permanent_error_SM_not_present, bits)
   decode _ (0:1:0:0:b3:b2:b1:b0:bits)
      -- 0100 1010 ~ 0100 1111
      | 10 <= (bits4ToInt [b3,b2,b1,b0]) && (bits4ToInt [b3,b2,b1,b0]) <= 15
         = (TP_ST_Permanent_error_Reserved (bits4ToInt [b3,b2,b1,b0]), bits)
      | otherwise = error ("[decode] TP_ST_Permanent_error_Reserved "
           ++ show [b3,b2,b1,b0])
   decode _ (0:1:0:1:b3:b2:b1:b0:bits)
      -- 0101 0000 ~ 0101 1111
      = (TP_ST_Permanent_error_Values_specific_to_SC
           (bits4ToInt [b3,b2,b1,b0]), bits)

   decode _ (0:1:1:0:0:0:0:0:bits) = (TP_ST_Temporary_failure_Congenstion, bits)
   decode _ (0:1:1:0:0:0:0:1:bits) = (TP_ST_Temporary_failure_SME_busy, bits)
   decode _ (0:1:1:0:0:0:1:0:bits) 
      = (TP_ST_Temporary_failure_No_response_from_SME, bits)
   decode _ (0:1:1:0:0:0:1:1:bits) 
      = (TP_ST_Temporary_failure_Service_rejected, bits)
   decode _ (0:1:1:0:0:1:0:0:bits) 
      = (TP_ST_Temporary_failure_Quality_of_service_unavailable, bits)
   decode _ (0:1:1:0:0:1:0:1:bits) 
      = (TP_ST_Temporary_failure_Error_in_SME, bits)
   decode _ (0:1:1:0:b3:b2:b1:b0:bits)                  
      -- 0110 0110 ~ 0110 1001
      | 6 <= bits4ToInt [b3,b2,b1,b0] &&  bits4ToInt [b3,b2,b1,b0] <= 9
          = (TP_ST_Temporary_failure_Reserved1 (bits4ToInt [b3,b2,b1,b0]), bits)
      | 10 <= bits4ToInt [b3,b2,b1,b0] && bits4ToInt [b3,b2,b1,b0] <= 15
          = (TP_ST_Temporary_failure_Reserved2
               (bits4ToInt [b3,b2,b1,b0]), bits)
      | otherwise = error ("[decode] TP_ST_Temporary_failure_Reserved1,2 "
                                 ++ show (bits4ToInt [b3,b2,b1,b0]))
   decode _ (0:1:1:1:b3:b2:b1:b0:bits)
      -- 0111 0000 ~ 0111 1111
      = (TP_ST_Temporary_failure_Values_specific_to_SC
            (bits4ToInt [b3,b2,b1,b0]), bits)

   decode _ (1:b6:b5:b4:b3:b2:b1:b0:bits)               -- 1XXXXXXX
      = (TP_ST_Reserved (bits8ToInt [0,b6,b5,b4,b3,b2,b1,b0]), bits)

instance Variant TP_ST where
   valid = oneof [ 
             elements [
               TP_ST_Short_msg_received_by_the_SME,
               TP_ST_Short_msg_failed_to_confirm_delivery,
               TP_ST_Short_msg_replaced_by_the_SC ],

             -- 0000 0011 ~ 0000 1111
             liftM TP_ST_Short_msg_transaction_complted_Reserved
                (choose (3,15)),

             elements [
               TP_ST_Temporary_error_Congestion,
               TP_ST_Temporary_error_SME_busy,
               TP_ST_Temporary_error_No_response_from_SME,
               TP_ST_Temporary_error_Service_rejected,
               TP_ST_Temporary_error_Quality_of_service_unavailable,
               TP_ST_Temporary_error_Error_in_SME ],

             -- 0010 0110 ~ 0010 1111
             liftM TP_ST_Temporary_error_Reserved
                (choose (2^2+2^1, 2^3+2^2+2^1+2^0)),

             -- 0011 0000 ~ 0011 1111
             liftM TP_ST_Temporary_error_Values_specific_to_SC
                (choose (0, 2^3+2^2+2^1+2^0)),

             elements [
               TP_ST_Permanent_error_Remote_procedure_error,
               TP_ST_Permanent_error_Incompatible_destination,
               TP_ST_Permanent_error_Connection_rejected_by_SME,
               TP_ST_Permanent_error_Not_obtaineable,
               TP_ST_Permanent_error_Quality_of_service_unavailable,
               TP_ST_Permanent_error_No_interworking_available,
               TP_ST_Permanent_error_SM_validity_peirod_expired,
               TP_ST_Permanent_error_SM_deleted_by_originating_SME,
               TP_ST_Permanent_error_SM_deleted_by_SC_administration,
               TP_ST_Permanent_error_SM_not_present ],

             -- 0100 1010 ~ 0100 1111
             liftM TP_ST_Permanent_error_Reserved
               (choose (2^3+2^1, 2^3+2^2+2^1+2^0)),

             -- 0101 0000 ~ 0101 1111
             liftM TP_ST_Permanent_error_Values_specific_to_SC
               (choose (0, 2^3+2^2+2^1+2^0)),

             elements [
               TP_ST_Temporary_failure_Congenstion,
               TP_ST_Temporary_failure_SME_busy,
               TP_ST_Temporary_failure_No_response_from_SME,
               TP_ST_Temporary_failure_Service_rejected,
               TP_ST_Temporary_failure_Quality_of_service_unavailable,
               TP_ST_Temporary_failure_Error_in_SME ],

             -- 0110 0110 ~ 0110 1001
             liftM TP_ST_Temporary_failure_Reserved1
               (choose (2^2+2^1, 2^3+2^0)),

             -- 0110 1010 ~ 0110 1111
             liftM TP_ST_Temporary_failure_Reserved2
               (choose (2^3+2^1, 2^3+2^2+2^1+2^0)),

             -- 0111 0000 ~ 0111 1111
             liftM TP_ST_Temporary_failure_Values_specific_to_SC
               (choose (0, 2^3+2^2+2^1+2^0)),

             -- 1XXXXXXX
             liftM TP_ST_Reserved (choose (0, 2^7-1)) ] 
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Reply-Path (TP-RP)
--------------------------------------------------------------------------------
data TP_RP = TP_RP Bool
     deriving (Show, Eq)

instance BitRep TP_RP a where
   encode _ (TP_RP False) = [0]
   encode _ (TP_RP True)  = [1]

   decode _ (0:bits) = (TP_RP False, bits)
   decode _ (1:bits) = (TP_RP True, bits)

instance Variant TP_RP where
   valid = liftM TP_RP valid
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Message-Number (TP-MN)
--------------------------------------------------------------------------------
data TP_MN = TP_MN Int
     deriving (Show, Eq)

instance BitRep TP_MN a where
   encode _ (TP_MN i)
      | 0<=i && i<=255 = intToBits8 i
      | otherwise      = error ("[encode] TP_MN " ++ show i)

   decode _ (b7:b6:b5:b4:b3:b2:b1:b0:bits)
      | 0<=(bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]) && (bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0])<=255 = (TP_MN (bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]), bits)
      | otherwise      = error ("[decode] TP_MN " ++ show [b7,b6,b5,b4,b3,b2,b1,b0])
   decode _ bits = error ("[decode] TP_MN " ++ show bits)

instance Variant TP_MN where
   valid = do i <- choose (0,255)
              return(TP_MN i)
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Command-Type (TP-CT)
--------------------------------------------------------------------------------
data TP_CT =
     TP_CT_Enquiry_on_submitted_short_message -- 00000000 SRR==1
   | TP_CT_Cancel_status_report_request     -- 00000001 SRR==0
   | TP_CT_Delete_submitted_short_message   -- 00000010 SRR==0
   | TP_CT_Enable_status_report_request     -- 00000011 SRR==0
   | TP_CT_Reserved Int                     -- 00000100~00011111 SRR=Unspecified
   | TP_CT_Values_specific_to_SC Int        -- 11100000~11111111 SRR=1or0
     deriving (Show, Eq)

isTP_CT_Enquiry_on_submitted_short_message 
   TP_CT_Enquiry_on_submitted_short_message = True
isTP_CT_Enquiry_on_submitted_short_message _ = False

isTP_CT_Cancel_status_report_request
   TP_CT_Cancel_status_report_request = True
isTP_CT_Cancel_status_report_request _ = False

isTP_CT_Delete_submitted_short_message
   TP_CT_Delete_submitted_short_message = True
isTP_CT_Delete_submitted_short_message _ = False

isTP_CT_Enable_status_report_request
   TP_CT_Enable_status_report_request = True
isTP_CT_Enable_status_report_request _ = False

isTP_CT_Reserved (TP_CT_Reserved _) = True
isTP_CT_Reserved (_) = False

isTP_CT_Values_specific_to_SC (TP_CT_Values_specific_to_SC _) = True
isTP_CT_Values_specific_to_SC (_) = False

instance BitRep TP_CT TP_SRR where
   encode TP_SRR_Status_Report_Requested
          TP_CT_Enquiry_on_submitted_short_message = [0,0,0,0,0,0,0,0]
   encode TP_SRR_No_Status_Report_Requested
          TP_CT_Cancel_status_report_request       = [0,0,0,0,0,0,0,1]
   encode TP_SRR_No_Status_Report_Requested
          TP_CT_Delete_submitted_short_message     = [0,0,0,0,0,0,1,0]
   encode TP_SRR_No_Status_Report_Requested
          TP_CT_Enable_status_report_request       = [0,0,0,0,0,0,1,1]
   encode _ (TP_CT_Reserved i)
      -- 000 00100 ~ 000 11111
      | 4 <= i && i <= 31 = [0,0,0] ++ drop 3 (intToBits8 i)
      | otherwise = error ("[encode] TP_CT_Reserved "++ show i)
   encode _ (TP_CT_Values_specific_to_SC i)
      -- 111 00000 ~ 111 11111
      | 0 <= i && i <= 31 = [1,1,1] ++ drop 3 (intToBits8 i)
      | otherwise = error ("[encode] TP_CT_Values_specific_to_SC "++ show i)

   decode TP_SRR_Status_Report_Requested (0:0:0:0:0:0:0:0:bits)
      = (TP_CT_Enquiry_on_submitted_short_message, bits)
   decode TP_SRR_No_Status_Report_Requested (0:0:0:0:0:0:0:1:bits) 
      = (TP_CT_Cancel_status_report_request, bits)
   decode TP_SRR_No_Status_Report_Requested (0:0:0:0:0:0:1:0:bits) 
      = (TP_CT_Delete_submitted_short_message, bits)
   decode TP_SRR_No_Status_Report_Requested (0:0:0:0:0:0:1:1:bits) 
      = (TP_CT_Enable_status_report_request, bits)
   decode _ (0:0:0:b4:b3:b2:b1:b0:bits)             
      -- 000 00100 ~ 000 11111
      | 4 <= (bits8ToInt[0,0,0,b4,b3,b2,b1,b0]) 
          && (bits8ToInt [0,0,0,b4,b3,b2,b1,b0]) <= 31
           = (TP_CT_Reserved (bits8ToInt[0,0,0,b4,b3,b2,b1,b0]), bits)
      | otherwise 
           = error ("[encode] TP_CT_Reserved "
                        ++ show (0:0:0:b4:b3:b2:b1:b0:bits))
   decode _ (1:1:1:b4:b3:b2:b1:b0:bits)         
      -- 111 00000 ~ 111 11111
      | 0 <= bits8ToInt [0,0,0,b4,b3,b2,b1,b0] 
          && bits8ToInt [0,0,0,b4,b3,b2,b1,b0] <= 31 
           = (TP_CT_Values_specific_to_SC
                 (bits8ToInt [0,0,0,b4,b3,b2,b1,b0]), bits)
      | otherwise = error ("[encode] TP_CT_Values_specific_to_SC "
                       ++ show (0:0:0:b4:b3:b2:b1:b0:bits))

instance Variant TP_CT where
   valid = oneof [
             elements [
               TP_CT_Enquiry_on_submitted_short_message,
               TP_CT_Cancel_status_report_request,
               TP_CT_Delete_submitted_short_message,
               TP_CT_Enable_status_report_request
             ],

             -- 000 00100 ~ 000 11111
             liftM TP_CT_Reserved (choose (4,31)), 

             -- 111 00000 ~ 111 11111
             liftM TP_CT_Values_specific_to_SC (choose (0,31)) ]

   invalid = valid

--------------------------------------------------------------------------------
-- TP-Command-Data-Length (TP-CDL)
--------------------------------------------------------------------------------
data TP_CDL = TP_CDL Int
     deriving (Show, Eq)

instance BitRep TP_CDL a where
   encode _ (TP_CDL i) = intToBits8 i
   
   decode _ (b7:b6:b5:b4:b3:b2:b1:b0:bits) = (TP_CDL (bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]), bits)

instance Variant TP_CDL where
   valid = do i <- choose (0,157)
              return (TP_CDL i)
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Command-Data (TP-CD)
--------------------------------------------------------------------------------
data TP_CD = TP_CD [Int] -- 157 octets
     deriving (Show, Eq)

lenTP_CD (TP_CD octets) = length octets

instance BitRep TP_CD TP_CDL where
   encode (TP_CDL i) (TP_CD octets)
      | and (map (\x -> 0 <= x && x <= 255) octets)
            {- TBD : && 0 <= i && i <= 157 -}
            {- TBD : && length octets == i -}
          = concat (map intToBits8 octets)
      | otherwise = error ("[encode] TP_CD "++ show octets)

   decode (TP_CDL i) bits
      | True {- TBD : 0 <= i && i <= 157 && i <= length bits * 8 -} = 
        let g n (b7:b6:b5:b4:b3:b2:b1:b0:bits) =
                let (octets0, bits0) = g (n-1) bits
                in  (bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0] : octets0, bits0)
            g 0 bits = ([], bits)

            (octets1, bits1) = g i bits
        in  (TP_CD octets1, bits1)
              
      | otherwise = error ("[decode] TP_CD "++ show i ++ ", " ++ show bits)

instance Variant TP_CD where
   valid = do len <- choose (0, 157)
              str <- getRandomText len
              return (TP_CD (map Data.Char.ord str))

   invalid = valid

--------------------------------------------------------------------------------
-- TP-Failure-Cause (TP-FCS)
--------------------------------------------------------------------------------
data TP_FCS = TP_FCS Int
     deriving (Show, Eq)

instance BitRep TP_FCS a where
   encode _ (TP_FCS i) = intToBits8 i

   decode _ (b7:b6:b5:b4:b3:b2:b1:b0:bits) = (TP_FCS (bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]), bits)
   decode _ bits = error ("[decode] TP_FCS "++ show bits)

instance Variant TP_FCS where
   valid = liftM TP_FCS (choose (0,2^8-1))
   invalid = valid

--------------------------------------------------------------------------------
-- TP-User-Data-Header-Indicator (TP-UDHI)
--------------------------------------------------------------------------------
data TP_UDHI = TP_UDHI Bool
     deriving (Eq, Show)

isTP_UDHI (TP_UDHI b) = b

instance BitRep TP_UDHI a where
   encode _ (TP_UDHI False) = [0]
   encode _ (TP_UDHI True)  = [1]

   decode _ (0:bits) = (TP_UDHI False, bits)
   decode _ (1:bits) = (TP_UDHI True, bits)
   decode _ bits = error ("[decode] TP_UDHI " ++ show bits)

instance Variant TP_UDHI where
   valid = liftM TP_UDHI (elements [ False ])
   invalid = valid

--------------------------------------------------------------------------------
-- TP-User Data (TP-UD)
--------------------------------------------------------------------------------
data TP_UD =
     TP_UD_NoUDH Int                 -- UDL  
                 String              -- Short message
   | TP_UD_UDH   Int                 -- UDL
                 Int                 -- UDHL
                 [(Int, Int, [Int])] -- (IEI,IEIDL,IED)*
                 String              -- Short message
     deriving (Show, Eq)

isTP_UD_NoUDH (TP_UD_NoUDH _ _) = True
isTP_UD_NoUDH (_) = False

isTP_UD_UDH (TP_UD_UDH _ _ _ _) = True
isTP_UD_UDH (_) = False

lenTP_UD (TP_UD_NoUDH udl _) = udl
lenTP_UD (TP_UD_UDH udl _ _ _) = udl

instance BitRep TP_UD (TP_UDHI, Character_Set) where
   encode (TP_UDHI False, GSM7Bit) (TP_UD_NoUDH udl short_msg)
      = intToBits8 udl ++ bytesToGsm7bit short_msg
   encode (TP_UDHI False, CS_8Bit) (TP_UD_NoUDH udl short_msg)
      = intToBits8 udl ++ bytesToCS8bit short_msg
   encode (TP_UDHI False, UCS2_16Bit) (TP_UD_NoUDH udl short_msg)
      = intToBits8 (udl * 2) ++ bytesToUCS16bit short_msg
   encode (TP_UDHI True, cs) (TP_UD_UDH udl udhl ieis short_msg)
      | 0 <= udl  && udl  <= 255 &&
        0 <= udhl && udhl <= 255 &&
        and (map (\(iei,ieidl,ieid)-> 0 <= iei 
                      && iei <= 255 && 0 <= ieidl && ieidl <= 255) ieis)
         = intToBits8 udl ++ 
           intToBits8 udhl ++ 
           concat (map (\(iei,ieidl,ieid)-> intToBits8 iei 
                      ++ intToBits8 ieidl 
                      ++ concat (map intToBits8 ieid)) ieis)
              ++ concat (map (intToBits8 . Data.Char.ord) short_msg)
      | otherwise 
         = error ("[encode] TP_UD " ++ ", " ++ show cs ++ ", " ++ show udl 
                     ++ ", " ++ show udhl ++ ", " ++ show ieis 
                     ++ ", " ++ short_msg)

   encode (tp_udhi, cs) tp_ud
      = error ("[encode] TP_UD : " ++ show tp_udhi ++ ", " ++ show cs 
                  ++ ", " ++ show tp_ud)


   decode (TP_UDHI False, GSM7Bit) (b7: b6 : b5 : b4 : b3 : b2 : b1 : b0 : bits)
      = let len = bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]
            (s, bits') = gsm7bitToBytes len bits
        in  (TP_UD_NoUDH len s, bits')

   decode (TP_UDHI False, CS_8Bit) (b7: b6 : b5 : b4 : b3 : b2 : b1 : b0 : bits)
      = let len = bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]
            (s, bits') = cs8bitToBytes len bits
        in  (TP_UD_NoUDH len s, bits')

   decode (TP_UDHI False, UCS2_16Bit) (b7: b6 : b5 : b4 : b3 : b2 : b1 : b0 : bits)
      = let len = bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]
            (s, bits') = ucs16bitToBytes (len `div` 2) bits
        in  (TP_UD_NoUDH (len `div` 2) s, bits')

   decode (tp_udhi, cs) bits = error ("[decode] TP_UD : tp_udhi=" ++ show tp_udhi ++ ", cs=" ++ show cs ++ ", bits=" ++ show bits)

instance Variant TP_UD where
   valid = do maxLen <- elements [140, 158, 159, 140, 151, 152, 160, 
                                  140, 70, 255]
              len <- choose (0, maxLen)
              str <- getRandomText len
              return (TP_UD_NoUDH len str)
              {- TBD : TP_UD_UDH -}

   invalid = valid

--------------------------------------------------------------------------------
-- TP-Reject-Duplicates (TP-RD)
--------------------------------------------------------------------------------
data TP_RD = TP_RD Bool
     deriving (Show, Eq)

instance BitRep TP_RD a where
   encode _ (TP_RD False) = [0]
   encode _ (TP_RD True)  = [1]

   decode _ (0:bits) = (TP_RD False, bits)
   decode _ (1:bits) = (TP_RD True, bits)
   decode _ bits = error ("[decode] TP_RD " ++ show bits)

instance Variant TP_RD where
   valid = liftM TP_RD valid
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Status-Report-Qualifier (TP-SRQ)
--------------------------------------------------------------------------------
data TP_SRQ = TP_SRQ Bool
     deriving (Show, Eq)

instance BitRep TP_SRQ a where
   encode _ (TP_SRQ False) = [0]
   encode _ (TP_SRQ True)  = [1]

   decode _ (0:bits) = (TP_SRQ False, bits)
   decode _ (1:bits) = (TP_SRQ True, bits)
   decode _ bits = error ("[decode] TP_SRQ " ++ show bits)

instance Variant TP_SRQ where 
   valid = liftM TP_SRQ valid
   invalid = valid

--------------------------------------------------------------------------------
-- TP-Parameter-Indicator (TP-PI)
--------------------------------------------------------------------------------
data TP_PI = TP_PI Bool   -- Extension bit
                   Int    -- 4 Reserved bits
                   Bool   -- TP-UDL
                   Bool   -- TP-DCS
                   Bool   -- TP-PID
     deriving (Show, Eq)

instance BitRep TP_PI a where
   encode _ (TP_PI extension i udl dcs pid) 
      | 0 <= i && i <= 15 = 
         let
            b7 = if extension then 1 else 0
            b2 = if udl then 1 else 0
            b1 = if dcs then 1 else 0
            b0 = if pid then 1 else 0
         in 
            [b7] ++ drop 4 (intToBits8 i) ++ [b2,b1,b0]
      | otherwise = error ("[encode] TP_PI " ++ show extension ++ ", " 
                             ++ show i ++ ", " ++ show udl ++ ", " 
                             ++ show dcs ++ ", " ++ show pid)

   decode _ (b7:b6:b5:b4:b3:b2:b1:b0:bits)
      = (TP_PI extension (bits4ToInt [b6,b5,b4,b3]) udl dcs pid, bits)
      where
         extension = b7 == 1
         udl = b2 == 1
         dcs = b1 == 1
         pid = b0 == 1
   decode _ bits = error ("[decode] TP_PI " ++ show bits)

instance Variant TP_PI where
   valid = liftM5 TP_PI valid (choose (0,2^4-1)) valid valid valid
   invalid = valid 

--------------------------------------------------------------------------------
-- TP-UDL
--------------------------------------------------------------------------------
data TP_UDL = TP_UDL Int deriving (Eq, Show)

instance BitRep TP_UDL a where
   encode _ (TP_UDL i)
      | 0 <= i && i <= 2^8-1 = intToBits8 i
      | otherwise = error ("[encode] TP_UDL : " ++ show i)

   decode _ (b7:b6:b5:b4:b3:b2:b1:b0:bits)
      = (TP_UDL (bits8ToInt [b7,b6,b5,b4,b3,b2,b1,b0]), bits)

instance Variant TP_UDL where
   valid = liftM TP_UDL (choose (0,2^8-1))   
   invalid = valid

--------------------------------------------------------------------------------
-- SMS PDUs
--------------------------------------------------------------------------------
data SMS_PDU =
       SMS_Deliver TP_MMS TP_RP TP_UDHI TP_SRI TP_OA TP_PID TP_DCS TP_SCTS TP_UD
          {- 140 bytes -}

     | SMS_Deliver_Report_for_RP_NAck TP_UDHI TP_FCS TP_PI (Maybe TP_PID)
          (Maybe TP_DCS) {- (Maybe TP_UDL) -} (Maybe TP_UD) {- 158 bytes  -}

     | SMS_Deliver_Report_for_RP_Ack TP_UDHI TP_PI TP_SCTS (Maybe TP_PID)
          (Maybe TP_DCS) {- (Maybe TP_UDL) -} (Maybe TP_UD) {- 159 bytes  -}

     | SMS_Submit TP_RD TP_VPF TP_RP TP_UDHI TP_SRR TP_MR TP_DA TP_PID TP_DCS
          (Maybe TP_VP) TP_UD {- 140 bytes -}

     | SMS_Submit_Report_for_RP_NAck TP_UDHI TP_FCS TP_PI TP_SCTS 
          (Maybe TP_PID) (Maybe TP_DCS) {- (Maybe TP_UDL) -} (Maybe TP_UD)
          {- 151 bytes -}

     | SMS_Submit_Report_for_RP_Ack TP_UDHI TP_PI TP_SCTS (Maybe TP_PID)
          (Maybe TP_DCS) {- (Maybe TP_UDL) -} (Maybe TP_UD) {- 152 bytes -}

     | SMS_Status_Report TP_UDHI TP_MMS TP_SRQ TP_MR TP_RA TP_SCTS TP_DT TP_ST
          TP_PI (Maybe TP_PID) (Maybe TP_DCS) {- (Maybe TP_UDL) -} (Maybe TP_UD)
          {- Dependent on TP-DCS
               GSM alphabet, 7bit : 160 characters
               8-bite data : 140 characters
               UCS2, 16bit : 70 complex characters
          -}
     | SMS_Command TP_UDHI TP_SRR TP_MR TP_PID TP_CT TP_MN
          TP_DA TP_CDL (Maybe TP_CD) {- Dependent on TP-CDL : # of octets -}
       deriving (Show, Eq)


isSMS_Deliver (SMS_Deliver _ _ _ _ _ _ _ _ _) = True
isSMS_Deliver (_) = False

isSMS_Deliver_Report_for_RP_NAck (SMS_Deliver_Report_for_RP_NAck _ _ _ _ _ _ ) = True
isSMS_Deliver_Report_for_RP_NAck (_) = False

isSMS_Deliver_Report_for_RP_Ack (SMS_Deliver_Report_for_RP_Ack _ _ _ _ _ _) = True
isSMS_Deliver_Report_for_RP_Ack (_) = False

isSMS_Submit_Report_for_RP_NAck (SMS_Submit_Report_for_RP_NAck _ _ _ _ _ _ _) = True
isSMS_Submit_Report_for_RP_NAck (_) = False

isSMS_Submit_Report_for_RP_Ack (SMS_Submit_Report_for_RP_Ack _ _ _ _ _ _) = True
isSMS_Submit_Report_for_RP_Ack (_) = False

isSMS_Submit (SMS_Submit _ _ _ _ _ _ _ _ _ _ _) = True
isSMS_Submit (_) = False

isSMS_Status_Report (SMS_Status_Report _ _ _ _ _ _ _ _ _ _ _ _) = True
isSMS_Status_Report (_) = False

isSMS_Command (SMS_Command _ _ _ _ _ _ _ _ _) = True
isSMS_Command (_) = False


instance BitRep SMS_PDU (Direction, Maybe Acknowledgement) where

   encode (MStoSC,Nothing) (SMS_Submit tp_rd tp_vpf tp_rp tp_udhi
                               tp_srr tp_mr tp_da tp_pid tp_dcs 
                               maybe_tp_vp tp_ud)
      = encode () tp_rp ++
        encode () tp_udhi ++
        encode () tp_srr ++
        encode () tp_vpf ++
        encode () tp_rd ++
        encode (MStoSC, Nothing :: Maybe Acknowledgement) SMS_SUBMIT ++
        encode () tp_mr ++
        encode () tp_da ++
        encode () tp_pid ++
        encode () tp_dcs ++
        encode (tp_vpf /= TP_VP_Field_Not_Present, tp_vpf) maybe_tp_vp ++
        encode (tp_udhi,dcsToCharacterSet tp_dcs) tp_ud

   encode (SCtoMS,Just Ack) (SMS_Submit_Report_for_RP_Ack tp_udhi
                                tp_pi tp_scts maybe_tp_pid maybe_tp_dcs
                                -- maybe_tp_udl
                                maybe_tp_ud)
      = let (TP_PI ext_bit reserved_4bits flag_tp_udl flag_tp_dcs flag_tp_pid)
               = tp_pi
        in
        [0] ++
        encode () tp_udhi ++ 
        [0,0,0,0] ++
        encode (SCtoMS, Just Ack) SMS_SUBMIT_REPORT_ACK ++
        encode () tp_pi ++
        encode () tp_scts ++
        encode (flag_tp_pid, ()) maybe_tp_pid ++
        encode (flag_tp_dcs, ()) maybe_tp_dcs ++
        -- encode (flag_tp_udl, ()) maybe_tp_udl ++
        encode (flag_tp_udl {- && fromJust maybe_tp_udl /= TP_UDL 0 -},
                   (tp_udhi, 
                    if isJust maybe_tp_dcs
                    then dcsToCharacterSet (fromJust maybe_tp_dcs)
                    else GSM7Bit)) maybe_tp_ud

   encode (SCtoMS,Just NAck) (SMS_Submit_Report_for_RP_NAck tp_udhi tp_fcs
                                 tp_pi tp_scts maybe_tp_pid maybe_tp_dcs
                                 -- maybe_tp_udl
                                 maybe_tp_ud)
      = let (TP_PI ext_bit reserved_4bits flag_tp_udl flag_tp_dcs flag_tp_pid)
               = tp_pi
        in
        [0] ++
        encode () tp_udhi ++
        [0,0,0,0] ++
        encode (SCtoMS,Just NAck) SMS_SUBMIT_REPORT_NACK ++
        encode () tp_fcs ++
        encode () tp_pi ++
        encode () tp_scts ++
        encode (flag_tp_pid, ()) maybe_tp_pid ++
        encode (flag_tp_dcs, ()) maybe_tp_dcs ++
        -- encode (flag_tp_udl, ()) maybe_tp_udl ++
        encode (flag_tp_udl {- && fromJust maybe_tp_udl /= TP_UDL 0 -},
                   (tp_udhi, 
                    if isJust maybe_tp_dcs
                    then dcsToCharacterSet (fromJust maybe_tp_dcs)
                    else GSM7Bit)) maybe_tp_ud

   encode (SCtoMS, Nothing) (SMS_Deliver tp_mms tp_rp tp_udhi tp_sri tp_oa
                                tp_pid tp_dcs tp_scts tp_ud)
      = encode () tp_rp ++
        encode () tp_udhi ++
        encode () tp_sri ++
        [0,0] ++ 
        encode () tp_mms ++
        encode (SCtoMS, Nothing :: Maybe Acknowledgement) SMS_DELIVER ++
        encode () tp_oa ++
        encode () tp_pid ++
        encode () tp_dcs ++
        encode () tp_scts ++
        encode (tp_udhi, dcsToCharacterSet tp_dcs) tp_ud

   encode (MStoSC, Just Ack) (SMS_Deliver_Report_for_RP_Ack tp_udhi tp_pi
                                 tp_scts maybe_tp_pid maybe_tp_dcs
                                 -- maybe_tp_udl
                                 maybe_tp_ud)
      = let (TP_PI ext_bit reserved_4bits flag_tp_udl flag_tp_dcs flag_tp_pid)
               = tp_pi
        in
        [0] ++
        encode () tp_udhi ++
        [0,0,0,0] ++
        encode (MStoSC, Just Ack) SMS_DELIVER_REPORT_ACK ++
        encode () tp_pi ++
        encode () tp_scts ++        
        encode (flag_tp_pid, ()) maybe_tp_pid ++        
        encode (flag_tp_dcs, ()) maybe_tp_dcs ++
        -- encode (flag_tp_udl, ()) maybe_tp_udl ++

        encode (flag_tp_udl {- && fromJust maybe_tp_udl /= TP_UDL 0 -},
                   (tp_udhi, 
                    if isJust maybe_tp_dcs
                    then dcsToCharacterSet (fromJust maybe_tp_dcs)
                    else GSM7Bit)) maybe_tp_ud

   encode (MStoSC, Just NAck) (SMS_Deliver_Report_for_RP_NAck tp_udhi tp_fcs
                                  tp_pi maybe_tp_pid maybe_tp_dcs
                                  -- maybe_tp_udl
                                  maybe_tp_ud)
      = let (TP_PI ext_bit reserved_4bits flag_tp_udl flag_tp_dcs flag_tp_pid)
             = tp_pi
        in
        [0] ++
        encode () tp_udhi ++
        [0,0,0,0] ++
        encode (MStoSC, Just NAck) SMS_DELIVER_REPORT_NACK ++
        encode () tp_fcs ++
        encode () tp_pi ++
        encode (flag_tp_pid, ()) maybe_tp_pid ++
        encode (flag_tp_dcs, ()) maybe_tp_dcs ++
        -- encode (flag_tp_udl, ()) maybe_tp_udl ++
        encode (flag_tp_udl {- && fromJust maybe_tp_udl /= TP_UDL 0 -},
                   (tp_udhi, 
                    if isJust maybe_tp_dcs
                    then dcsToCharacterSet (fromJust maybe_tp_dcs)
                    else GSM7Bit)) maybe_tp_ud

   encode (SCtoMS, Nothing) (SMS_Status_Report tp_udhi tp_mms tp_srq tp_mr
       tp_ra tp_scts tp_dt tp_st tp_pi maybe_tp_pid maybe_tp_dcs 
       -- maybe_tp_udl
       maybe_tp_ud)
      = let (TP_PI ext_bit reserved_4bits flag_tp_udl flag_tp_dcs flag_tp_pid)
             = tp_pi
        in
        [0] ++
        encode () tp_udhi ++
        encode () tp_srq ++ 
        [0,0] ++
        encode () tp_mms ++
        encode (SCtoMS, Nothing ::  Maybe Acknowledgement) SMS_STATUS_REPORT ++
        encode () tp_mr ++
        encode () tp_ra ++
        encode () tp_scts ++
        encode () tp_dt ++
        encode () tp_st ++
        encode () tp_pi ++
        encode (flag_tp_pid, ()) maybe_tp_pid ++
        encode (flag_tp_dcs, ()) maybe_tp_dcs ++
        -- encode (flag_tp_udl, ()) maybe_tp_udl ++
        encode (flag_tp_udl {- && fromJust maybe_tp_udl /= TP_UDL 0 -},
                   (tp_udhi, 
                    if isJust maybe_tp_dcs
                    then dcsToCharacterSet (fromJust maybe_tp_dcs)
                    else GSM7Bit)) maybe_tp_ud

   encode (MStoSC, Nothing) (SMS_Command tp_udhi tp_srr tp_mr  tp_pid tp_ct
        tp_mn tp_da tp_cdl maybe_tp_cd)
      = [0] ++
        encode () tp_udhi ++
        encode () tp_srr ++ 
        [0,0,0] ++
        encode (MStoSC,Nothing ::  Maybe Acknowledgement) SMS_COMMAND ++
        encode () tp_mr ++ 
        encode () tp_pid ++
        encode (tp_srr) tp_ct ++
        encode () tp_mn ++ 
        encode () tp_da ++ 
        encode () tp_cdl ++ 
        encode (tp_cdl /= TP_CDL 0, tp_cdl) maybe_tp_cd 

   encode dir_maybe_ack sms_pdu
      = error ("[encode] SMS_PDU : " ++ show dir_maybe_ack
                  ++ ", " ++ show sms_pdu)


   {- MStoSC/Nothing : SMS_SUBMIT, SMS_COMMAND -}
   decode (MStoSC, Nothing) bits   
      = let (tp_mti, _) 
               = case bits of 
                   (b7:b6:b5:b4:b3:b2:b1:b0:bitss) -> 
                      decode (MStoSC, Nothing :: Maybe Acknowledgement)
                         (b1:b0:bitss)
                   _ -> error ("[decode] MStoSC/Nothing : " ++ show bits)
        in
        case tp_mti of 
          SMS_SUBMIT ->
            let 
               (tp_rp,       bits2)  = decode () bits
               (tp_udhi,     bits3)  = decode () bits2
               (tp_srr,      bits4)  = decode () bits3
               (tp_vpf,      bits5)  = decode () bits4
               (tp_rd,       bits6)  = decode () bits5
               (_,           bits7)
                   = decode (MStoSC, Nothing :: Maybe Acknowledgement) bits6
                     :: (TP_MTI, [Int])
               (tp_mr,       bits8)  = decode () bits7
               (tp_da,       bits9)  = decode () bits8
               (tp_pid,      bits10) = decode () bits9
               (tp_dcs,      bits11) = decode () bits10
               (maybe_tp_vp, bits12) 
                  = decode (tp_vpf /= TP_VP_Field_Not_Present, tp_vpf) bits11
               (tp_ud,       bits13) 
                  = decode (tp_udhi, dcsToCharacterSet tp_dcs) bits12
            in (SMS_Submit tp_rd tp_vpf tp_rp tp_udhi tp_srr tp_mr tp_da
                  tp_pid tp_dcs maybe_tp_vp tp_ud, bits13)

          SMS_COMMAND -> 
            let
               (_, bits2)       = (take 1 bits, drop 1 bits)
               (tp_udhi, bits3) = decode () bits2 
               (tp_srr, bits4)  = decode () bits3
               (_, bits5)       = (take 3 bits4, drop 3 bits4)
               (_, bits6)       
                  = decode (MStoSC, Nothing :: Maybe Acknowledgement) bits5
                    :: (TP_MTI, [Int])
               (tp_mr, bits7)   = decode () bits6
               (tp_pid, bits8)  = decode () bits7
               (tp_ct, bits9)   = decode (tp_srr) bits8
               (tp_mn, bits10)  = decode () bits9
               (tp_da, bits11)  = decode () bits10
               (tp_cdl, bits12) = decode () bits11
               (maybe_tp_cd, bits13)
                  = decode (tp_cdl /= TP_CDL 0, tp_cdl) bits12
            in (SMS_Command tp_udhi tp_srr tp_mr tp_pid tp_ct tp_mn tp_da
                  tp_cdl maybe_tp_cd, bits13)
          _ -> error ("[decode] (MStoSC,Nothing) " ++ show bits)


   {- MStoSC/Just acknowledgement : SMS_DELIVER_REPORT_ACK/NACK  -}
   decode (MStoSC, Just acknowledgement) bits  
      = let (tp_udhi,(tp_mti, bits1)) = case bits of
               (b7:b6:b5:b4:b3:b2:b1:b0:bits') ->
                   (fst (decode () (b6:b5:b4:b3:b2:b1:b0:bits')),
                         decode (MStoSC, Just acknowledgement) (b1:b0:bits'))
               _ -> error ("[decode] SCtoMS " ++ show (Just acknowledgement)
                              ++ ", " ++ show bits)
        in
          case tp_mti of
            SMS_DELIVER_REPORT_ACK ->
               let
                  (tp_pi,        bits2) = decode () bits1
                  (TP_PI ext_bit reserved_4bits flag_tp_udl flag_tp_dcs
                      flag_tp_pid) = tp_pi
                  (tp_scts,      bits3) = decode () bits2
                  (maybe_tp_pid, bits4) = decode (flag_tp_pid, ()) bits3
                  (maybe_tp_dcs, bits5) = decode (flag_tp_dcs, ()) bits4
                  -- (maybe_tp_udl, bits6) = decode (flag_tp_udl, ()) bits5
                  bits6 = bits5
                  (maybe_tp_ud,  bits7) 
                     = decode (flag_tp_udl {- && fromJust maybe_tp_udl /= TP_UDL 0 -},
                          (tp_udhi,
                           if isJust maybe_tp_dcs
                           then dcsToCharacterSet (fromJust maybe_tp_dcs)
                           else GSM7Bit)) bits6
               in
                  (SMS_Deliver_Report_for_RP_Ack tp_udhi tp_pi tp_scts
                      maybe_tp_pid maybe_tp_dcs {- maybe_tp_udl -} maybe_tp_ud, bits7)

            SMS_DELIVER_REPORT_NACK ->
               let
                  (tp_fcs,       bits2) = decode () bits1
                  (tp_pi,        bits3) = decode () bits2
                  (TP_PI ext_bit reserved_4bits flag_tp_udl flag_tp_dcs
                      flag_tp_pid) = tp_pi
                  (maybe_tp_pid, bits4) = decode (flag_tp_pid, ()) bits3
                  (maybe_tp_dcs, bits5) = decode (flag_tp_dcs, ()) bits4
                  -- (maybe_tp_udl, bits6) = decode (flag_tp_udl, ()) bits5
                  bits6 = bits5
                  (maybe_tp_ud,  bits7) 
                      = decode (flag_tp_udl 
                                {- && fromJust maybe_tp_udl /= TP_UDL 0 -} , 
                           (tp_udhi,
                            if isJust maybe_tp_dcs
                            then dcsToCharacterSet (fromJust maybe_tp_dcs)
                            else GSM7Bit)) bits6
               in
                  (SMS_Deliver_Report_for_RP_NAck tp_udhi tp_fcs tp_pi 
                      maybe_tp_pid maybe_tp_dcs {- maybe_tp_udl -} maybe_tp_ud, bits7)

            _ -> error ("[decode] MStoSC : " ++ show tp_mti ++ ", "
                          ++ show (Just acknowledgement) ++ ", " ++ show bits)


   {- SCtoMS/Nothing : SMS_DELIVER, SMS_STATUS_REPORT -}
   decode (SCtoMS, Nothing) bits 
      = let (tp_mti,_) = case bits of
               (b7:b6:b5:b4:b3:b2:b1:b0:bits') ->
                   decode (SCtoMS,Nothing :: Maybe Acknowledgement)
                      (b1:b0:bits')
               _ -> error ("[decode] (SCtoMS,Nothing) " ++ show bits)
        in 
          case tp_mti of 
            SMS_DELIVER -> 
              let
                 (tp_rp, bits2)    = decode () bits
                 (tp_udhi, bits3)  = decode () bits2
                 (tp_sri, bits4)   = decode () bits3
                 (_, bits5)        = (take 2 bits4, drop 2 bits4)
                 (tp_mms, bits6)   = decode () bits5
                 (_, bits7) 
                    = decode (SCtoMS, Nothing :: Maybe Acknowledgement) bits6
                      :: (TP_MTI, [Int])
                 (tp_oa, bits8)    = decode () bits7
                 (tp_pid, bits9)   = decode () bits8
                 (tp_dcs, bits10)  = decode () bits9
                 (tp_scts, bits11) = decode () bits10
                 (tp_ud, bits12)
                    = decode (tp_udhi, dcsToCharacterSet tp_dcs) bits11
              in  
                 (SMS_Deliver tp_mms tp_rp tp_udhi tp_sri tp_oa tp_pid
                     tp_dcs tp_scts tp_ud, bits12)

            SMS_STATUS_REPORT ->
              let 
                  (_, bits2)        = (take 1 bits, drop 1 bits)
                  (tp_udhi, bits3)  = decode () bits2
                  (tp_srq, bits4)   = decode () bits3
                  (_, bits5)        = (take 2 bits4, drop 2 bits4)
                  (tp_mms, bits6)   = decode () bits5
                  (_, bits7)        
                     = decode (SCtoMS, Nothing :: Maybe Acknowledgement) bits6
                       :: (TP_MTI, [Int])
                  (tp_mr, bits8)    = decode () bits7
                  (tp_ra, bits9)    = decode () bits8
                  (tp_scts, bits10) = decode () bits9
                  (tp_dt, bits11)   = decode () bits10
                  (tp_st, bits12)   = decode () bits11
                  (tp_pi, bits13)   = decode () bits12

                  (TP_PI ext_bit reserved_4bits flag_tp_udl flag_tp_dcs
                      flag_tp_pid) = tp_pi

                  (maybe_tp_pid, bits14) = decode (flag_tp_pid, ()) bits13
                  (maybe_tp_dcs, bits15) = decode (flag_tp_dcs, ()) bits14
                  -- (maybe_tp_udl, bits16) = decode (flag_tp_udl, ()) bits15
                  bits16 = bits15
                  (maybe_tp_ud,  bits17)
                      = decode (flag_tp_udl 
                                {- && fromJust maybe_tp_udl /= TP_UDL 0 -} ,
                           (tp_udhi,
                            if flag_tp_dcs 
                            then dcsToCharacterSet (fromJust maybe_tp_dcs)
                            else GSM7Bit)) bits16
              in
                  (SMS_Status_Report tp_udhi tp_mms tp_srq tp_mr tp_ra tp_scts
                    tp_dt tp_st tp_pi maybe_tp_pid maybe_tp_dcs {- maybe_tp_udl -}
                      maybe_tp_ud, bits17)

            _ -> error ("[decode] (SCtoMS,Nothing) " ++ show tp_mti 
                          ++ ", " ++ show bits)

   decode (SCtoMS, Just acknowledgement) bits  {- SMS_SUBMIT_REPORT_ACK/NACK  -}
      = let (tp_udhi,(tp_mti, bits1)) = case bits of
               (b7:b6:b5:b4:b3:b2:b1:b0:bits') ->
                   (fst (decode () (b6:b5:b4:b3:b2:b1:b0:bits')),
                         decode (SCtoMS, Just acknowledgement) (b1:b0:bits'))
               _ -> error ("[decode] SCtoMS " ++ show (Just acknowledgement)
                             ++ ", " ++ show bits)
        in
           case tp_mti of 
              SMS_SUBMIT_REPORT_ACK ->
                let 
                  (tp_pi,   bits2) = decode () bits1
                  (tp_scts, bits3) = decode () bits2
                  (TP_PI ext_bit reserved_4bits flag_tp_udl flag_tp_dcs
                      flag_tp_pid) = tp_pi
                  (maybe_tp_pid, bits4) = decode (flag_tp_pid, ()) bits3
                  (maybe_tp_dcs, bits5) = decode (flag_tp_dcs, ()) bits4
                  -- (maybe_tp_udl, bits6) = decode (flag_tp_udl, ()) bits5
                  bits6 = bits5
                  (maybe_tp_ud,  bits7)
                      = decode (flag_tp_udl 
                                {- && fromJust maybe_tp_udl /= TP_UDL 0 -} ,
                           (tp_udhi,
                            if flag_tp_dcs 
                            then dcsToCharacterSet (fromJust maybe_tp_dcs)
                            else GSM7Bit)) bits6
                in  (SMS_Submit_Report_for_RP_Ack tp_udhi tp_pi tp_scts
                        maybe_tp_pid maybe_tp_dcs {- maybe_tp_udl -} maybe_tp_ud,
                           bits7)

              SMS_SUBMIT_REPORT_NACK ->
                let
                  (tp_fcs,       bits2) = decode () bits1
                  (tp_pi,        bits3) = decode () bits2
                  (tp_scts,      bits4) = decode () bits3
                  (TP_PI ext_bit reserved_4bits flag_tp_udl flag_tp_dcs
                      flag_tp_pid) = tp_pi
                  (maybe_tp_pid, bits5) = decode (flag_tp_pid, ()) bits4
                  (maybe_tp_dcs, bits6) = decode (flag_tp_dcs, ()) bits5
                  -- (maybe_tp_udl, bits7) = decode (flag_tp_udl, ()) bits6
                  bits7 = bits6
                  (maybe_tp_ud,  bits8) 
                      = decode (flag_tp_udl 
                                {- && fromJust maybe_tp_udl /= TP_UDL 0 -} , 
                           (tp_udhi,
                            if flag_tp_dcs
                            then dcsToCharacterSet (fromJust maybe_tp_dcs)
                            else GSM7Bit)) bits7
                in  (SMS_Submit_Report_for_RP_NAck tp_udhi tp_fcs tp_pi
                        tp_scts maybe_tp_pid maybe_tp_dcs {- maybe_tp_udl-}
                        maybe_tp_ud, bits8)

              _ -> error ("[decode] SCtoMS : " ++ show tp_mti ++ ", " 
                           ++ show (Just acknowledgement) ++ ", " ++ show bits)

instance Variant SMS_PDU where
   valid = let
            genSmsSubmit = 
              do tp_rd <- valid :: Gen TP_RD
                 tp_vpf <- valid
                 tp_rp <- valid
                 tp_udhi <- valid
                 tp_srr <- valid
                 tp_mr <- valid
                 tp_da <- valid
                 tp_pid <- valid
                 tp_dcs <- valid
                 maybe_tp_vp <- valid `suchThat`
                    (\maybe_tp_vp ->
                         isTP_VP_Field_Not_Present tp_vpf
                         && isNothing maybe_tp_vp
                      || isTP_VP_Field_Present_Relative tp_vpf
                         && isJust maybe_tp_vp
                         && isTP_VP_Relative (fromJust maybe_tp_vp)
                      || isTP_VP_Field_Present_Absolute tp_vpf
                         && isJust maybe_tp_vp
                         && isTP_VP_Absolute (fromJust maybe_tp_vp)
                      || isTP_VP_Field_Present_Enhanced tp_vpf
                         && isJust maybe_tp_vp
                         && isTP_VP_Enhanced (fromJust maybe_tp_vp) )
                 tp_ud <- valid `suchThat`
                   (\tp_ud -> 
                         isTP_UDHI tp_udhi==False 
                         && isTP_UD_NoUDH tp_ud
                         && lenTP_UD tp_ud * (dcsToBytesPerChar tp_dcs) <= 140
                      || isTP_UDHI tp_udhi==True 
                         && isTP_UD_UDH tp_ud
                         && lenTP_UD tp_ud * (dcsToBytesPerChar tp_dcs) <= 140)

                 return
                   (SMS_Submit tp_rd tp_vpf tp_rp tp_udhi
                      tp_srr tp_mr tp_da tp_pid tp_dcs maybe_tp_vp tp_ud)

            genSmsSubmitRpAck =
              do tp_udhi <- valid 
                 tp_pi@(TP_PI ext_bit reserved_int
                           flag_tp_udl flag_tp_dcs flag_tp_pid) <- valid
                 tp_scts <- valid
                 maybe_tp_pid <- valid `suchThat` 
                    (\maybe_tp_pid ->
                         flag_tp_pid==True  && isJust maybe_tp_pid
                       || flag_tp_pid==False && isNothing maybe_tp_pid)
                 maybe_tp_dcs <- valid `suchThat`
                    (\maybe_tp_dcs ->
                         flag_tp_dcs==True  && isJust maybe_tp_dcs
                      || flag_tp_dcs==False && isNothing maybe_tp_dcs)
--                  maybe_tp_udl <- valid `suchThat`
--                     (\maybe_tp_udl ->
--                          flag_tp_udl==True  && isJust maybe_tp_udl
--                       || flag_tp_udl==False && isNothing maybe_tp_udl)
                 maybe_tp_ud <- valid `suchThat` 
                    (\maybe_tp_ud ->
                         flag_tp_udl==True  && isJust maybe_tp_ud
                         && lenTP_UD (fromJust maybe_tp_ud)
                            * (if flag_tp_dcs && isJust maybe_tp_dcs 
                               then dcsToBytesPerChar (fromJust maybe_tp_dcs)
                               else 1) <= 152
                      || flag_tp_udl==False && isNothing maybe_tp_ud)

                 return (SMS_Submit_Report_for_RP_Ack tp_udhi tp_pi
                            tp_scts maybe_tp_pid maybe_tp_dcs
                               {- maybe_tp_udl -} maybe_tp_ud)

            genSmsSubmitRpNack =
              do tp_udhi <- valid
                 tp_fcs <- valid
                 tp_pi@(TP_PI ext_bit reserved_int flag_tp_udl
                                  flag_tp_dcs flag_tp_pid) <- valid
                 tp_scts <- valid
                 maybe_tp_pid <- valid `suchThat` 
                    (\maybe_tp_pid ->
                         flag_tp_pid==True  && isJust maybe_tp_pid
                      || flag_tp_pid==False && isNothing maybe_tp_pid)
                 maybe_tp_dcs <- valid `suchThat`
                    (\maybe_tp_dcs ->
                         flag_tp_dcs==True  && isJust maybe_tp_dcs
                      || flag_tp_dcs==False && isNothing maybe_tp_dcs)
--                  maybe_tp_udl <- valid `suchThat`
--                     (\maybe_tp_udl ->
--                          flag_tp_udl==True  && isJust maybe_tp_udl
--                       || flag_tp_udl==False  && isNothing maybe_tp_udl)
                 maybe_tp_ud <- valid `suchThat` 
                    (\maybe_tp_ud ->
                         flag_tp_udl==True  && isJust maybe_tp_ud
                         && lenTP_UD (fromJust maybe_tp_ud) *
                             (if flag_tp_dcs && isJust maybe_tp_dcs 
                               then dcsToBytesPerChar (fromJust maybe_tp_dcs)
                               else 1)<= 151
                      || flag_tp_udl==False && isNothing maybe_tp_ud)

                 return (SMS_Submit_Report_for_RP_NAck tp_udhi tp_fcs
                            tp_pi tp_scts maybe_tp_pid maybe_tp_dcs 
                                {- maybe_tp_udl -} maybe_tp_ud)

            genSmsDeliver = 
              do tp_mms <- valid
                 tp_rp <- valid
                 tp_udhi <- valid
                 tp_sri <- valid
                 tp_oa <- valid
                 tp_pid <- valid
                 tp_dcs <- valid
                 tp_scts <- valid
                 tp_ud <- valid `suchThat`
                    (\tp_ud ->
                        isTP_UDHI tp_udhi==False && isTP_UD_NoUDH tp_ud
                        && lenTP_UD tp_ud * dcsToBytesPerChar tp_dcs <= 140
                     || isTP_UDHI tp_udhi==True  && isTP_UD_UDH tp_ud
                        && lenTP_UD tp_ud * dcsToBytesPerChar tp_dcs <= 140)

                 return (SMS_Deliver tp_mms tp_rp tp_udhi tp_sri tp_oa
                            tp_pid tp_dcs tp_scts tp_ud)

            genSmsDeliverRpAck =
              do tp_udhi <- valid
                 tp_pi@(TP_PI ext_bit reserved_int
                           flag_tp_udl flag_tp_dcs flag_tp_pid) <- valid
                 tp_scts <- valid
                 maybe_tp_pid <- valid `suchThat` 
                    (\maybe_tp_pid ->
                         flag_tp_pid==True  && isJust maybe_tp_pid
                      || flag_tp_pid==False && isNothing maybe_tp_pid)
                 maybe_tp_dcs <- valid `suchThat`
                    (\maybe_tp_dcs ->
                         flag_tp_dcs==True  && isJust maybe_tp_dcs
                      || flag_tp_dcs==False && isNothing maybe_tp_dcs)
--                  maybe_tp_udl <- valid `suchThat`
--                     (\maybe_tp_udl ->
--                          flag_tp_udl==True  && isJust maybe_tp_udl
--                       || flag_tp_udl==False && isNothing maybe_tp_udl)
                 maybe_tp_ud <- valid `suchThat`
                    (\maybe_tp_ud ->
                         flag_tp_udl==True  && isJust maybe_tp_ud
                         && lenTP_UD (fromJust maybe_tp_ud) *
                            (if flag_tp_dcs && isJust maybe_tp_dcs
                             then dcsToBytesPerChar (fromJust maybe_tp_dcs)
                             else 1)
                             <= 159
                      || flag_tp_udl==False && isNothing maybe_tp_ud)

                 return (SMS_Deliver_Report_for_RP_Ack tp_udhi tp_pi
                    tp_scts maybe_tp_pid maybe_tp_dcs {- maybe_tp_udl -}
                       maybe_tp_ud)

            genSmsDeliverRpNack =
              do tp_udhi <- valid
                 tp_fcs <- valid
                 tp_pi@(TP_PI ext_bit reserved_int 
                           flag_tp_udl flag_tp_dcs flag_tp_pid) <- valid
                 maybe_tp_pid <- valid `suchThat` 
                    (\maybe_tp_pid ->
                         flag_tp_pid==True  && isJust maybe_tp_pid
                      || flag_tp_pid==False && isNothing maybe_tp_pid)
                 maybe_tp_dcs <- valid `suchThat`
                    (\maybe_tp_dcs ->
                         flag_tp_dcs==True  && isJust maybe_tp_dcs
                      || flag_tp_dcs==False && isNothing maybe_tp_dcs)
--                  maybe_tp_udl <- valid `suchThat`
--                     (\maybe_tp_udl ->
--                          flag_tp_udl==True  && isJust maybe_tp_udl
--                       || flag_tp_udl==False && isNothing maybe_tp_udl)
                 maybe_tp_ud <- valid `suchThat`
                    (\maybe_tp_ud ->
                         flag_tp_udl==True && isJust maybe_tp_ud
                         && lenTP_UD (fromJust maybe_tp_ud) *
                            (if flag_tp_dcs && isJust maybe_tp_dcs
                             then dcsToBytesPerChar (fromJust maybe_tp_dcs)
                             else 1)
                            <= 158
                      || flag_tp_udl==False && isNothing maybe_tp_ud)

                 return (SMS_Deliver_Report_for_RP_NAck tp_udhi tp_fcs
                    tp_pi maybe_tp_pid maybe_tp_dcs
                      {- maybe_tp_udl -} maybe_tp_ud)

            genSmsStatusReport = 
              do tp_udhi <- valid 
                 tp_mms <- valid
                 tp_srq <- valid
                 tp_mr <- valid
                 tp_ra <- valid
                 tp_scts <- valid
                 tp_dt <- valid 
                 tp_st <- valid
                 tp_pi@(TP_PI ext_bit reserved_int flag_tp_udl
                           flag_tp_dcs flag_tp_pid) <- valid
                 maybe_tp_pid <- valid `suchThat`
                    (\maybe_tp_pid ->
                         flag_tp_pid==True  && isJust maybe_tp_pid
                       || flag_tp_pid==False && isNothing maybe_tp_pid)
                 maybe_tp_dcs <- valid `suchThat`
                    (\maybe_tp_dcs ->
                         flag_tp_dcs==True  && isJust maybe_tp_dcs
                      || flag_tp_dcs==False && isNothing maybe_tp_dcs)
--                  maybe_tp_udl <- valid `suchThat`
--                     (\maybe_tp_udl ->
--                          flag_tp_udl==True  && isJust maybe_tp_udl
--                       || flag_tp_udl==False && isNothing maybe_tp_udl)
                 maybe_tp_ud <- valid `suchThat`
                    (\maybe_tp_ud ->
                         flag_tp_udl==True  && isJust maybe_tp_ud
                         && lenTP_UD (fromJust maybe_tp_ud) *
                            (if flag_tp_dcs && isJust maybe_tp_dcs
                             then dcsToBytesPerChar (fromJust maybe_tp_dcs)
                             else 1)
                            <= 160
                      || flag_tp_udl==False && isNothing maybe_tp_ud)

                 return (SMS_Status_Report tp_udhi tp_mms tp_srq tp_mr tp_ra
                           tp_scts tp_dt tp_st tp_pi maybe_tp_pid maybe_tp_dcs
                           {- maybe_tp_udl -} maybe_tp_ud)

            genSmsCommand = 
              do tp_udhi <- valid
                 tp_srr <- valid
                 tp_mr <- valid
                 tp_pid <- valid
                 tp_ct <- valid `suchThat` 
                    (\tp_ct ->
                          isTP_CT_Enquiry_on_submitted_short_message tp_ct
                          && isTP_SRR_Status_Report_Requested tp_srr
                       || isTP_CT_Cancel_status_report_request tp_ct
                          && isTP_SRR_No_Status_Report_Requested tp_srr
                       || isTP_CT_Delete_submitted_short_message tp_ct
                          && isTP_SRR_No_Status_Report_Requested tp_srr
                       || isTP_CT_Enable_status_report_request tp_ct
                          && isTP_SRR_No_Status_Report_Requested tp_srr
                       || isTP_CT_Reserved tp_ct
                       || isTP_CT_Values_specific_to_SC tp_ct)
                 tp_mn <- valid
                 tp_da <- valid
                 tp_cdl <- valid 
                 maybe_tp_cd <- valid `suchThat` 
                    (\maybe_tp_cd ->
                         case tp_cdl of
                            TP_CDL len ->
                                 len == 0 && isNothing maybe_tp_cd
                              || len > 0 && isJust maybe_tp_cd
                                 && lenTP_CD (fromJust maybe_tp_cd) == len)
                                 -- Could be too slow to generate!
                 return (SMS_Command tp_udhi tp_srr tp_mr tp_pid tp_ct tp_mn
                            tp_da tp_cdl maybe_tp_cd)

           in oneof [ genSmsSubmit, genSmsSubmitRpAck, genSmsSubmitRpNack, 
                      genSmsDeliver, genSmsDeliverRpAck, genSmsDeliverRpNack,
                      genSmsStatusReport, genSmsCommand
                    ]

   invalid = valid               

--------------------------------------------------------------------------------
-- SMSC Information
--------------------------------------------------------------------------------
data SMSC_Information = SMSC_Information AddrFields
     deriving (Show, Eq)

instance BitRep SMSC_Information a where
   encode _ (SMSC_Information addrfields) = encode () addrfields

   decode _ bits = let (addrfields,bits') = decode () bits
                  in  (SMSC_Information addrfields, bits')

instance Variant SMSC_Information where
   valid = liftM SMSC_Information valid
   invalid = valid

data SMS_Pdu_With_SMSC = SMS_Pdu_With_SMSC SMSC_Information SMS_PDU
     deriving (Show, Eq)

instance BitRep SMS_Pdu_With_SMSC (Direction, Maybe Acknowledgement) where
   encode (dir, maybe_acknow) (SMS_Pdu_With_SMSC smsc sms_pdu) = 
      encode () smsc ++
      encode (dir,maybe_acknow) sms_pdu

   decode (dir, maybe_acknow) bits = 
      let (smsc, bits1) = decode () bits
          (sms_pdu, bits2) = decode (dir, maybe_acknow) bits1
      in  (SMS_Pdu_With_SMSC smsc sms_pdu, bits2)

instance Variant SMS_Pdu_With_SMSC where
   valid = liftM2 SMS_Pdu_With_SMSC valid valid
   invalid = valid

--------------------------------------------------------------------------------
-- Test Suite
--------------------------------------------------------------------------------

data OptionArg = Normal | GenC | Send

test_suite option = 
   let f (sms_pdu,i) = 
          let (dir,ack) = 
                if isSMS_Submit sms_pdu
                then (MStoSC, Nothing :: Maybe Acknowledgement)
                else if isSMS_Deliver sms_pdu
                then (SCtoMS, Nothing :: Maybe Acknowledgement)
                else if isSMS_Deliver_Report_for_RP_Ack sms_pdu
                then (MStoSC, Just Ack)
                else if isSMS_Deliver_Report_for_RP_NAck sms_pdu
                then (MStoSC, Just NAck)
                else if isSMS_Submit_Report_for_RP_Ack sms_pdu
                then (SCtoMS, Just Ack)
                else if isSMS_Submit_Report_for_RP_NAck sms_pdu
                then (SCtoMS, Just NAck)
                else if isSMS_Status_Report sms_pdu
                then (SCtoMS, Nothing)
                else if isSMS_Command sms_pdu
                then (MStoSC, Nothing)
                else error ("[test_suite] Not Supported : " ++ show sms_pdu)

              bits = encode (dir,ack) sms_pdu
              (sms_pdu',bits') = decode (dir,ack) bits
              sanity_test = sms_pdu == sms_pdu' && bits' == []

          in  (i, (sms_pdu, bits, sms_pdu', bits', sanity_test))

       toCHex (b7:b6:b5:b4:b3:b2:b1:b0:hexs) = 
          do putStr ( "0x" ++ [bits4ToHexdigit [b7,b6,b5,b4]]
                           ++ [bits4ToHexdigit [b3,b2,b1,b0]] )
             (if null hexs then return ()
              else do { putStr ", "; toCHex hexs })
       toCHex [] = return ()

       g GenC (i, (sms_pdu, bits, sms_pdu', bits', sanity_test)) =
          do putStrLn ("/* sms_pdu" ++ show i)
             putStrLn (show sms_pdu)
             putStrLn (each8Bits bits)
             putStrLn "*/"
             putStrLn ("int sms_pdu_len" ++ show i ++ " = "
                             ++ show (length bits `div` 8) ++ ";\n" )
             putStrLn ("char sms_pdu" ++ show i ++ "[]= {")
             toCHex bits
             putStrLn "};"
             (if sanity_test
              then putStrLn ""
              else putStrLn ("\n" ++ show sms_pdu' ++ "\n" ++ show bits'))

       g Normal (i, (sms_pdu, bits, sms_pdu', bits', sanity_test)) =
          do putStrLn (show sms_pdu)
             putStrLn "->"
             putStrLn (bitsToHexString bits)
             (if sanity_test
              then putStrLn ""
              else putStrLn ("\n" ++ show sms_pdu' ++ "\n" ++ show bits'))

       g Send (i, (sms_pdu, bits, sms_pdu', bits', sanity_test)) =
          do let hexstr = bitsToHexString bits
             putStrLn (show sms_pdu)
             putStrLn "->"
             putStrLn hexstr 
             (if sanity_test
              then send (length hexstr) hexstr
              else putStrLn ("\n" ++ show sms_pdu' ++ "\n" ++ show bits'))

--        send len s_hexstr =
--           do h <- openFile "/dev/emr" WriteMode
--              let msg = concat
--                   [ 
--                      "LiMo.Test.SmsPdu.Event1", " ", "2", "\n",
--                      "int", " ", show len, "\n",
--                      "string", " ", s_hexstr, "\n"]
--              putStr msg
--              hPutStr h msg
--              hClose h

   in
     do sms_pdus1 <- mysample (valid :: Gen SMS_PDU)
        let sms_pdus = sms_pdus1 
        mapM_ (g option . f) (zip sms_pdus [1..])

-- | Generates some example values.
mysample :: Gen a -> IO [a]
mysample (MkGen m) =
  do rnd <- newQCGen
     let rnds rnd = rnd1 : rnds rnd2 where (rnd1,rnd2) = split rnd
     return [(m r n) | (r,n) <- rnds rnd `zip` [0,2..200] ]


send len s_hexstr =
   do h <- openFile "/dev/emr" WriteMode
      let msg = concat
                 [ 
                   "LiMo.Test.SmsPdu.Event1", " ", "2", "\n",
                   "int", " ", show len, "\n",
                   "string", " ", s_hexstr, "\n"
                 ]
      putStr msg
      myHPutStr h msg
      hFlush h
      hClose h

each8Bits [] = ""
each8Bits (b7:b6:b5:b4:b3:b2:b1:b0:bits)
   = show (b7:b6:b5:b4:b3:b2:b1:b0:[]) ++ " : "
     ++ bitsToHexString (b7:b6:b5:b4:b3:b2:b1:b0:[]) ++ "\n"
     ++ each8Bits bits

myHPutStr h []     = return ()
myHPutStr h (c:cs) =
   do hPutChar h c
      myHPutStr h cs

{-
SMS_Command (TP_UDHI False) TP_SRR_Status_Report_Requested (TP_MR 18) (TP_PID TP_PID_Bits7_6_SC_specific_use (TP_PID_Bits5_0_SC_Specific_Use 43)) (TP_CT_Reserved 9) (TP_MN 192) (TP_DA (AddrFields (AddrLen 5) (TypeOfAddr TON_Internation_number NPI_Private_numbering_plan) (AddrValue "984a6"))) (TP_CDL 80) (Just (TP_CD [89,111,117,32,97,114,101,32,100,105,115,104,111,110,101,115,116,44,32,98,117,116,32,110,101,118,101,114,32,116,111,32,116,104,101,32,112,111,105,110,116,32,111,102,32,104,117,114,116,105,110,103,32,97,32,102,114,105,101,110,100,46,89,111,117,32,97,114,101,32,99,97,112,97,98,108,101,32,111,102]))

LiMo.Test.SmsPdu.Event1 2
int 182
string 2212EB09C0059989C4F650596F752061726520646973686F6E6573742C20627574206E6576657220746F2074686520706F696E74206F662068757274696E67206120667269656E642E596F75206172652063617061626C65206F66
-}
      


{-

TODO
  : Relative => decomposition (Not so important!)

-}


--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------
-- sample_sms_submit =
--    SMS_Submit 
--      (TP_RD False) 
--      TP_VP_Field_Present_Relative
--      (TP_RP False)
--      (TP_UDHI False) 
--      TP_SRR_No_Status_Report_Requested

--      (TP_MR 10) 
--      (TP_DA   
--         (AddrFields (AddrLen 11)
--                     (TypeOfAddr TON_Unknown NPI_ISDN_Tel_numbering_plan)
--                     (AddrValue "01022188990")))
--      (TP_PID  
--         TP_PID_Bits7_6_00
--         (TP_PID_Bit5_Bits4_0
--             TP_PID_Bit5_Sme_to_sme_protocol
--             (TP_PID_Bits4_0_STSP 0)))
--      (TP_DCS_General False False Class0 GSM7Bit)  
--      (Just (TP_VP_Relative 167)) 
--      (TP_UD_NoUDH 11 "Hello World") 

-- sample_sms_submit_rp_ack =
--    SMS_Submit_Report_for_RP_Ack
--       (TP_UDHI False)
--       (TP_PI False 0 False False False)
--       (TP_SCTS 9 12 25 0 0 0 9)
--       Nothing
--       Nothing
--       Nothing
--       Nothing

-- sample_sms_submit_rp_nack =
--    SMS_Submit_Report_for_RP_NAck
--       (TP_UDHI False)
--       (TP_FCS (8*16 + 15))
--       (TP_PI False 0 False False False)
--       (TP_SCTS 10 2 12 0 0 0 9)
--       Nothing
--       Nothing
--       Nothing
--       Nothing       

-- sample_sms_deliver = 
--    SMS_Deliver
--      TP_MMS_No_More_Messages
--      (TP_RP False)
--      (TP_UDHI False)
--      TP_SRI_No_Status_Report_Indication
--      (TP_OA
--         (AddrFields (AddrLen 11)
--                     (TypeOfAddr TON_Unknown NPI_ISDN_Tel_numbering_plan)
--                     (AddrValue "01022188990")))
--      (TP_PID  
--         TP_PID_Bits7_6_00
--         (TP_PID_Bit5_Bits4_0
--             TP_PID_Bit5_Sme_to_sme_protocol
--             (TP_PID_Bits4_0_STSP 0)))

--      (TP_DCS_General False False Class0 GSM7Bit)  
--      (TP_SCTS 9 12 25 0 0 0 9)
--      (TP_UD_NoUDH 11 "Hello World") 

-- sample_sms_deliver_rep_ack = 
--    SMS_Deliver_Report_for_RP_Ack
--      (TP_UDHI False)
--      (TP_PI False 0 False False False)
--      (TP_SCTS 9 12 25 0 0 0 9)
--      Nothing --    (Maybe TP_PID)
--      Nothing --    (Maybe TP_DCS)
--      Nothing --    (Maybe TP_UDL)
--      Nothing --    (Maybe TP_UD)

-- sample_sms_deliver_rep_nack = 
--    SMS_Deliver_Report_for_RP_NAck  -- SMS-DELIVER-REPORT for RP-ERROR and Rp-ACK
--      (TP_UDHI False)
--      (TP_FCS (13*16 + 0))
--      (TP_PI False 0 False False False)
--      Nothing --    (Maybe TP_PID)
--      Nothing --    (Maybe TP_DCS)
--      Nothing --    (Maybe TP_UDL)
--      Nothing --    (Maybe TP_UD)

-- sample_sms_deliver_bits = "040BC87238880900F10000993092516195800AE8329BFD4697D9EC37"

-- test_suite1 =
--    [
--       decode (MStoSC,Nothing :: Maybe Acknowledgement) (encode (MStoSC,Nothing :: Maybe Acknowledgement) sample_sms_submit),
--       decode (SCtoMS, Just Ack) (encode (SCtoMS, Just Ack) sample_sms_submit_rp_ack),
--       decode (SCtoMS,Just NAck) (encode (SCtoMS,Just NAck) sample_sms_submit_rp_nack),
--       decode (SCtoMS,Nothing::Maybe Acknowledgement) (encode (SCtoMS,Nothing::Maybe Acknowledgement) sample_sms_deliver),
--       decode (MStoSC,Just Ack) (encode (MStoSC,Just Ack) sample_sms_deliver_rep_ack),
--       decode (MStoSC,Just NAck) (encode (MStoSC,Just NAck) sample_sms_deliver_rep_nack)
--    ] :: [ (SMS_PDU, [Int]) ]

{-

SMS_Status_Report (TP_UDHI False) TP_MMS_No_More_Messages (TP_SRQ False) (TP_MR 62) (TP_RA (AddrFields (AddrLen 7) (TypeOfAddr TON_Unknown NPI_National_numbering_plan) (AddrValue "49b89#a"))) (TP_SCTS 0 94 0 12 84 60 64) (TP_DT 74 30 47 17 15 47 (-5)) (TP_ST_Temporary_failure_Reserved2 13) (TP_PI True 8 True True True) (Just (TP_PID TP_PID_Bits7_6_01 (TP_PID_Bits5_0_ (TP_PID_Bits5_0_Reserved100000_111011 39)))) (Just (TP_DCS_General True False Class3 CS_8Bit)) (Just (TP_UD_NoUDH 104 "Q:\tWhat happens if you've got TWO flats?\nA:\tThey replace your generator.I don't know half of you half as"))

LiMo.Test.SmsPdu.Event1 2
int 262
string 063E0788948DA9FC00490021480646470374715174586DC7672768513A09576861742068617070656E7320696620796F7527766520676F742054574F20666C6174733F0A413A0954686579207265706C61636520796F75722067656E657261746F722E4920646F6E2774206B6E6F772068616C66206F6620796F752068616C66206173

-}

-- aa = send 262 "063E0788948DA9FC00490021480646470374715174586DC7672768513A09576861742068617070656E7320696620796F7527766520676F742054574F20666C6174733F0A413A0954686579207265706C61636520796F75722067656E657261746F722E4920646F6E2774206B6E6F772068616C66206F6620796F752068616C66206173\x00"

-- bbb = encode (SCtoMS, Nothing::Maybe Acknowledgement) (SMS_Status_Report (TP_UDHI False) TP_MMS_No_More_Messages (TP_SRQ False) (TP_MR 62) (TP_RA (AddrFields (AddrLen 7) (TypeOfAddr TON_Unknown NPI_National_numbering_plan) (AddrValue "49b89#a"))) (TP_SCTS 0 94 0 12 84 60 64) (TP_DT 74 30 47 17 15 47 (-5)) (TP_ST_Temporary_failure_Reserved2 13) (TP_PI True 8 True True True) (Just (TP_PID TP_PID_Bits7_6_01 (TP_PID_Bits5_0_ (TP_PID_Bits5_0_Reserved100000_111011 39)))) (Just (TP_DCS_General True False Class3 CS_8Bit)) (Just (TP_UD_NoUDH 104 "Q:\tWhat happens if you've got TWO flats?\nA:\tThey replace your generator.I don't know half of you half as"))) 

{-
SMS_Submit (TP_RD True) TP_VP_Field_Present_Relative (TP_RP True) (TP_UDHI False) TP_SRR_Status_Report_Requested (TP_MR 55) (TP_DA (AddrFields (AddrLen 16) (TypeOfAddr TON_Internation_number NPI_Telex_numbering_plan) (AddrValue "189*55080bc5911*"))) (TP_PID TP_PID_Bits7_6_00 (TP_PID_Bit5_Bits4_0 TP_PID_Bit5_Sme_to_sme_protocol (TP_PID_Bits4_0_STSP 23))) (TP_DCS_MWIG_Store_Msg_UnCompressed_UCS2 False OtherMsgWaiting) (Just (TP_VP_Relative 176)) (TP_UD_NoUDH 30 "You will have good luck and ov")
->
B537109481B95580D05E19B117E3B01E0059006F0075002000770069006C006C0020006800610076006500200067006F006F00640020006C00750063006B00200061006E00640020006F0076
-}

-- ddd = send 152 "B537109481B95580D05E19B117E3B01E0059006F0075002000770069006C006C0020006800610076006500200067006F006F00640020006C00750063006B00200061006E00640020006F0076\x00"

-- iddd = length "B537109481B95580D05E19B117E3B01E0059006F0075002000770069006C006C0020006800610076006500200067006F006F00640020006C00750063006B00200061006E00640020006F0076"

paper_example = SMS_Submit
  (TP_RD True)
  TP_VP_Field_Present_Absolute
  (TP_RP True)
  (TP_UDHI False)
  TP_SRR_Status_Report_Requested
  (TP_MR 122)
  (TP_DA
    (AddrFields
      (AddrLen 8)
      (TypeOfAddr
        TON_Alphanumeric_gsm7bit
        NPI_Service_center_specific_plan2)
      (AddrValue "a01b*7a2")))
  (TP_PID
    TP_PID_Bits7_6_00
    (TP_PID_Bit5_Bits4_0
    TP_PID_Bit5_Telematic_interworking
    TP_PID_Bits4_0_Specific_to_SC6))
  (TP_DCS_General
    False False Class3 GSM7Bit)
  (Just
    (TP_VP_Absolute 59 11 15 12 12 41 33))
  (TP_UD_NoUDH 3 "You")
