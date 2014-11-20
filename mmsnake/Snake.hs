{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}

import FreeGame
import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import System.Directory
import Control.Conditional
import System.Console.CmdArgs
import Data.List
import qualified Data.ByteString as BS
import qualified Data.Serialize as S

gridColor = (Color 0.8 0.8 0.8 1)
bgColor = white

drawGrid s = do
  clearColor bgColor
  vertLines 0
  horizLines 0
  where
    vertLines pos
      | pos < wW s = do
        dpos <- return $ fromIntegral pos
        color gridColor $ line [V2 dpos 0, V2 dpos (wH' s)]
        vertLines (cellSize s + pos + 1)
      | otherwise = return ()
    horizLines pos
      | pos < wH s = do
        dpos <- return $ fromIntegral pos
        color gridColor $ line [V2 0 dpos, V2 (wW' s) dpos]
        horizLines (cellSize s + pos + 1)
      | otherwise = return ()

drawSnake _ [] _ = return ()
drawSnake _ _ [] = return ()
drawSnake s (cell:cells) (bmp:bitmaps) = do
  translate (cellToCoord cell) $ bitmap bmp
  drawSnake s cells bitmaps
  where
    cellToCoord (V2 x y) = V2
                           (cellSize' s * (fromIntegral x) + (fromIntegral x) + 1 + cellSize' s / 2)
                           (cellSize' s * (fromIntegral y) + (fromIntegral y) + 1 + cellSize' s / 2)

drawAll s cells bitmaps target = do
  drawGrid s
  drawSnake s cells bitmaps
  drawSnake s [target] (drop (length cells) bitmaps)

--randCell :: Snake -> [V2 Int] -> Game (V2 Int)
randCell s snakeCells = do
  x <- randomness (0 :: Int, width s - 1)
  y <- randomness (0 :: Int, height s - 1)
  if (V2 (fromIntegral x) (fromIntegral y)) `elem` snakeCells && length snakeCells < width s * height s
    then randCell s snakeCells
    else return (V2 x y)


goTo _ [] _ _ = return []
goTo s cells@(sHead@(V2 fx fy):sTail) bitmaps point@(V2 x y)
  | fx == x && fy == y = return cells
  | otherwise = do
  drawGrid s
  drawSnake s cells bitmaps
  delay $ goTo s (nextMove:init cells) bitmaps point
  where
    nextMove = cond [(fx < x, V2 (fx + 1) fy),
                     (fx > x, V2 (fx - 1) fy),
                     (fy < y, V2 fx (fy + 1)),
                     (fy > y, V2 fx (fy - 1))]

performSteps _ [] _ _ = return []
performSteps _ cells _ [] = return cells
performSteps s cells@(sHead@(V2 fx fy):sTail) bitmaps ((V2 x y):steps) = do
  drawGrid s
  drawSnake s cells bitmaps
  delay $ performSteps s (V2 (fx + x) (fy + y) : init cells) bitmaps steps


-- no snake, shouldn't happen
game _ [] _ _ _ _ _ = return ()
game s cells@(sHead@(V2 fx fy):sTail) bitmaps direction target font end@(endInit, endSteps)
  | length bitmaps == length cells ||
    length cells > length endSteps = do
      cells' <- delay $ goTo s cells bitmaps endInit
      cells'' <- performSteps s cells' bitmaps endSteps
      foreverFrame $ do
        drawGrid s
        drawSnake s cells'' bitmaps
  | sHead `elem` sTail || fx < 0 || fy < 0 || fx >= (width s) || fy >= height s = do
    drawAll s cells bitmaps target
    translate (V2 ((wW' s) / 2 - 400) ((wH' s) / 2 - 200)) $
      color (Color 1 0 0 0.8) $ do
        text font 120 "Game over"
    condM [(keyPress KeySpace, gameReset s bitmaps font end),
           (otherwiseM, delay $ game s cells bitmaps direction target font end)]
  | otherwise = do
    curFps <- getFPS
    setTitle $ show sHead ++ " / " ++ show target ++ " / " ++ show curFps ++ " / " ++
      show (length cells) ++ "/" ++ show (length endSteps + 1)
    -- new direction
    nd <- condM [(keyPress KeyUp, changeDirection (V2 0 (-1))),
                 (keyPress KeyDown, changeDirection (V2 0 1)),
                 (keyPress KeyRight, changeDirection (V2 1 0)),
                 (keyPress KeyLeft, changeDirection (V2 (-1) 0)),
                 (otherwiseM, return direction)]
    -- move
    newCells <- return $ move nd
    newTarget <- if head newCells == target
                 then randCell s newCells
                 else return target
    -- draw
    drawAll s newCells bitmaps newTarget
    delay $ game s newCells bitmaps nd newTarget font end
  where
    -- simply add a new cell to that direction, and remove the last one
    move (V2 dx dy)
      | V2 (fx + dx) (fy + dy) == target = maybeBounds (V2 (fx + dx) (fy + dy)) : cells
      | otherwise = init $ maybeBounds (V2 (fx + dx) (fy + dy)) : cells
    -- cycle the snake in case if it's not allowed to die when meeting a wall
    maybeBounds (V2 x y)
      | walls s = V2 x y
      | x < 0 = V2 (width s - 1) y
      | y < 0 = V2 x (height s - 1)
      | x >= width s = V2 0 y
      | y >= height s = V2 x 0
      | otherwise = V2 x y
    -- change the direction, or don't
    changeDirection (V2 dx dy)
      | length sTail >= 1 && head sTail == maybeBounds (V2 (fx + dx) (fy + dy)) = return direction
      | otherwise = return (V2 dx dy)

gameReset settings bitmaps font end = do
  snakeCell <- randCell settings []
  target <- randCell settings [snakeCell]
  -- run game
  game settings [snakeCell] bitmaps (V2 0 0) target font end

-- initialization
gameInit settings images end = do
  -- set FPS
  setFPS $ fromIntegral $ fps settings
  -- set title
  box <- getBoundingBox
  setTitle $ show box
  -- preload bitmaps
  bitmaps <- forM images readBitmap
  forM_ bitmaps preloadBitmap
  font <- loadFont "Halo3.ttf"
  if drawMode settings
    then (drawPic settings (V2 0 0) bitmaps)
    else (gameReset settings bitmaps font end)

-- drawing
drawPic s cursor@(V2 x y) bitmaps = do
  drawGrid s
  drawSnake s [cursor] bitmaps
  condM [(keyPress KeySpace, delay $ storePic s [cursor] cursor [] cursor bitmaps),
         (keyPress KeyUp, iter (V2 x (y - 1))),
         (keyPress KeyDown, iter (V2 x (y + 1))),
         (keyPress KeyRight, iter (V2 (x + 1) y)),
         (keyPress KeyLeft, iter (V2 (x - 1) y)),
         (otherwiseM, iter cursor)]
  where
    iter p = delay $ drawPic s p bitmaps
      

storePic s cells cur@(V2 cx cy) moves cursor@(V2 x y) bitmaps = do
  drawAll s cells bitmaps cursor
  condM [(keyPress KeySpace, printMoves s (cx, cy) moves),
         (keyPress KeyUp, iter (V2 0 (-1))),
         (keyPress KeyDown, iter (V2 0 1)),
         (keyPress KeyRight, iter (V2 1 0)),
         (keyPress KeyLeft, iter (V2 (-1) 0)),
         (otherwiseM, delay $ storePic s cells cur moves cursor bitmaps)]
  where
    iter p@(V2 px py) = delay $ storePic s (cursor:cells) cur ((px, py):moves) (V2 (x + px) (y + py)) bitmaps

printMoves :: Snake -> (Int, Int) -> [(Int, Int)] -> Game ()
printMoves s initial moves = do
  embedIO $ BS.writeFile (endgame s) $ S.encode (initial, reverse moves)
  return ()

data Snake = Snake { width :: Int,
                     height :: Int,
                     cellSize :: Int,
                     imageDir :: String,
                     fps :: Int,
                     walls :: Bool,
                     drawMode :: Bool,
                     endgame :: String }
           deriving (Show, Data, Typeable)

wW s = (width s) * (cellSize s) + (width s) + 1
wH s = (height s) * (cellSize s) + (height s) + 1
wH' = fromIntegral . wH
wW' = fromIntegral . wW
cellSize' = fromIntegral . cellSize

settings = Snake { width = 57 &= help "width, in cells",
                   height = 36 &= help "height, in cells",
                   cellSize = 22 &= help "cells are square, this is a side size",
                   fps = 12 &= help "frames per second, frame is also a game tick",
                   walls = False &= help "die when running into a wall",
                   drawMode = False &= help "drawing mode",
                   imageDir = "icons/" &= help "a directory with pictures for snake cells",
                   endgame = "./endgame" &= help "endgame file"
                 } &=
           help "Run the snake game" &=
           summary "MM94 20th anniversary snake game" &=
           details ["A game where you control a snake that eats various images."]

main :: IO (Maybe ())
main = do
  s <- cmdArgs settings
  putStrLn $ "Settings: " ++ show s
  images <- getDirectoryContents $ imageDir s
  filtered <- filterM doesFileExist (map (imageDir s ++) images)
  endgameFile <- BS.readFile $ endgame s
  end <- return $ case S.decode endgameFile of
    (Left str) -> ((0,0), []) :: ((Int, Int), [(Int, Int)])
    (Right (steps :: ((Int, Int), [(Int, Int)]))) -> steps
  runGame Windowed (Box (V2 0 0) (V2 (wW' s) (wH' s))) $ gameInit s (sort filtered) (tupToV2 end)
  where
    tupToV2 ((x,y), l) = (V2 x y, map (\(x,y) -> V2 x y) l)
