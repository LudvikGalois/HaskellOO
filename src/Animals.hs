{-# Language DataKinds, FlexibleInstances, UndecidableInstances, FlexibleContexts, TypeFamilies, TemplateHaskell #-}

module Main where

import HaskellOO

-- Define some labels for methods
newMethod "makeNoise"
newMethod "eatFood"
newMethod "getAnimalName"
newMethod "hunt"
newMethod "countSheepEaten"

-- It's safe to make a method which already exists - it's a no-op if it already exists!
newMethod "eatFood"

animal self = do
  super <- object self -- Call object's constructor (because we're going to inherit from object)
  build $  makeNoise     .=. (error "called abstract method makeNoise" :: IO ())
       .*. eatFood       .=. (error "called abstract method eatFood" :: IO ())
       .*. getAnimalName .=. (error "called abstract method getAnimalName" :: IO String)
       .>. super -- Inherit from object

herbivore self = do
  super <- animal self
  -- Any redefined methods get overridden (you can call the old with super#method as you'd expect)
  build $  eatFood .=. ((self#getAnimalName) >>= (\x -> putStrLn $ "The " ++ x ++ " eats some grass"))
       .>. super
  
sheep self = do
  super <- herbivore self
  build $  makeNoise     .=. putStrLn "Baaa"
       .*. getAnimalName .=. returnIO "Sheep"
       .>. super

cow self = do
  super <- herbivore self
  build $  makeNoise     .=. putStrLn "Moo"
       .*. getAnimalName .=. returnIO "Cow"
       .>. super

carnivore self = do
  super <- animal self
  build $  eatFood .=. (self#getAnimalName >>= (\x -> putStrLn $ "The " ++ x ++ " eats some meat"))
       .*. hunt    .=. (self#getAnimalName >>= (\x -> putStrLn $ "The " ++ x ++ " is hunting"))
       .>. super

wolf self = do
  super <- carnivore self
  sheepEaten <- newIORef (0 :: Integer) -- A mutable "field"
  build $  eatFood .=. ((modifyIORef' sheepEaten succ) >> (self#getAnimalName) >>= (\x -> putStrLn $ "The " ++ x ++ " eats sheep"))
       .*. getAnimalName .=. returnIO "Wolf" 
       .*. makeNoise     .=. putStrLn "Aaahwoo"
       .*. countSheepEaten .=. readIORef sheepEaten
       .>. super

lion self = do
  super <- carnivore self
  build $  getAnimalName .=. returnIO "Lion"
       .*. makeNoise     .=. putStrLn "Roar"
       .>. super

main :: IO ()
main = do
  baatrick <- new sheep
  daisy    <- new cow
  arthur   <- new wolf
  mufasa   <- new lion
  putStrLn "Build a list of animals\n"
  -- (we can't append to an empty list though, and we can't up-cast, yet...)
  let animals = baatrick <: daisy <: arthur <: [mufasa]
  mapM_ (\x -> x#getAnimalName >>= putStrLn) animals
  putStrLn "----------------"
  putStrLn "Let's make some noise\n"
  mapM_ (#makeNoise) animals
  putStrLn "----------------"
  putStrLn "And now it's dinner time\n"
  mapM_ (#eatFood) animals
  putStrLn "----------------"
  putStrLn "Arthur the wolf is still hungry!\n"
  arthur#eatFood
  putStr "Arthur has eaten " >> (arthur#countSheepEaten) >>= putStr . show >> putStrLn " sheep"
