module IA where 

import Data.Ord
import List

data Suit = Club | Diamond | Spade | Heart
  deriving Eq

instance Show Suit where
  show Club    = "T"
  show Diamond = "D"
  show Spade   = "P"
  show Heart   = "C"

allSuits :: [Suit]
allSuits = [Club, Diamond, Spade, Heart]

data Number = Num2 | Num3 | Num4 | Num5 | Num6 | Num7
            | Num8 | Num9 | Num10 | NumJ | NumQ | NumK
            | NumA
  deriving (Eq, Ord)

instance Show Number where
  show Num2  = "2"
  show Num3  = "3"
  show Num4  = "4"
  show Num5  = "5"
  show Num6  = "6"
  show Num7  = "7"
  show Num8  = "8"
  show Num9  = "9"
  show Num10 = "10"
  show NumJ  = "J"
  show NumQ  = "Q"
  show NumK  = "K"
  show NumA  = "A"

allNumbers :: [Number]
allNumbers = [NumA, Num2, Num3, Num4, Num5, Num6,
              Num7, Num8, Num9, Num10, NumJ, NumQ,
              NumK]

data Card = Card Number Suit
  deriving Eq

cardNumber :: Card -> Number
cardNumber (Card number _) = number

cardSuit :: Card -> Suit
cardSuit (Card _ suit) = suit

instance Show Card where
  show (Card n s) = show n ++ show s

allCards :: [Card]
allCards = [Card n s | s <- allSuits, n <- allNumbers]

type Player = String

data Deal = DD {
                dealCards        :: [Card],
                dealFirstCard    :: Card,
                dealPlayers      :: [Player],
                dealAIPlayer     :: Player,
                dealAICards      :: [Card]
            }
  deriving Show

data Move = MM Player Card
  deriving Show

movePlayer :: Move -> Player
movePlayer (MM player _) = player

moveCard :: Move -> Card
moveCard (MM _ card) = card

type Trick = [Move]

data Round = RR Deal [Trick]
  deriving (Show)

mkRound :: Deal -> [Trick] -> Round
mkRound = RR

dealNextPlayer :: Deal -> Player -> Player
dealNextPlayer deal player = (!! 1) . dropWhile (/= player) . cycle . dealPlayers $ deal

roundDeal :: Round -> Deal
roundDeal (RR deal _) = deal 

roundTricks :: Round -> [Trick]
roundTricks (RR _ tricks) = tricks

numPlayers :: Deal -> Int
numPlayers = length . dealPlayers

trickComplete :: Round -> Trick -> Bool
trickComplete round t = length t == numPlayers (roundDeal round)

currentTrick :: Round -> Trick
currentTrick = head . roundTricks

previousTricks :: Round -> [Trick]
previousTricks = tail . roundTricks

currentTrickComplete :: Round -> Bool
currentTrickComplete round = trickComplete round $ currentTrick round

play :: Move -> Round -> Round
play move round
  | currentTrickComplete round = mkRound deal $ [move] : previousTricks round
  | otherwise = mkRound deal $ (currentTrick round ++ [move]) : previousTricks round
  where deal = roundDeal round

cardsPlayedBy :: Player -> Trick -> [Card]
cardsPlayedBy player trick = map moveCard (filter ((== player) . movePlayer) trick)

cardsInAIHand :: Round -> [Card]
cardsInAIHand round = foldr sub (dealAICards deal) tricks
  where sub trick cards = cards \\ cardsPlayedBy (dealAIPlayer deal) (currentTrick round)
        deal = roundDeal round
        tricks = roundTricks round

over :: (b -> b -> c) -> (a -> b) -> a -> a -> c
(*) `over` f = \x y -> f x * f y

trickTaker :: Trick -> Player
trickTaker []    = error "empty trick"
trickTaker trick = movePlayer $ maximumBy (comparing moveNumber) followSuit
  where followSuit = filter matchesSuit trick
        matchesSuit = (==) `over` moveSuit $ head trick
        moveNumber = cardNumber . moveCard
        moveSuit = cardSuit . moveCard

roundJustStarted :: Round -> Bool
roundJustStarted round = justOneTrick && noOnePlayed
  where
    justOneTrick = null . tail . roundTricks $ round
    noOnePlayed  = null (currentTrick round)

turnOfAI :: Round -> Bool
turnOfAI round
  | roundJustStarted round      = aiHasFirstCard
  | currentTrickComplete round  = aiTookCurrentTrick
  | otherwise                   = aiIsNextPlayer
  where
    deal               = roundDeal round
    tricks             = roundTricks round
    aiHasFirstCard     = dealFirstCard deal `elem` dealAICards deal
    aiTookCurrentTrick = trickTaker (currentTrick round) == dealAIPlayer deal
    aiIsNextPlayer     = dealNextPlayer deal lastPlayer == dealAIPlayer deal
    lastPlayer         = movePlayer . last . currentTrick $ round

aiBestCard :: Round -> Card
aiBestCard round
  | not (turnOfAI round)   = error "not the turn of AI"
  | roundJustStarted round = dealFirstCard deal
  | otherwise              = head (cardsInAIHand round)
  where deal = roundDeal round

----------

deal0 = DD {
          dealCards     = allCards,
          dealFirstCard = Card Num2 Club,
          dealPlayers   = ["N", "O", "S", "E"], -- CCW
          dealAIPlayer  = "S",
          dealAICards   = [Card Num3 Club, Card NumJ Spade, Card Num2 Club]
        }

round0 = RR deal0 [[]]
round1 = play (MM "S" (Card Num2 Club))    $ round0
round2 = play (MM "E" (Card Num2 Diamond)) $ round1
round3 = play (MM "N" (Card Num3 Diamond)) $ round2
round4 = play (MM "O" (Card Num4 Club))    $ round3
round5 = play (MM "O" (Card Num4 Heart))   $ round4

