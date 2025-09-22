import Game.Levels.Divisibility
-- Here's what we'll put on the title screen
Title "Prototype for a Heidelberg Lean Game"
Introduction
"
Welcome to the Prototype for a Heidelberg Lean Game!

In this game, you will explore a single world with 6 levels.
The final level (Level 6) proves that every prime number is irreducible.
This prototype is designed to demonstrate the structure and flow of a Lean game.
"

Info "
This game was created as part of the HEGL (Heidelberg Experimental Geometry Lab) Illustrating Mathematics Seminar 2024/2025 at the University of Heidelberg. For more details, visit the [Seminar page](https://matematiflo.github.io/HEGL_IMS_WiSe_2024/).

Credits:
- Adriano Messina
- Alina Stock
- Hanna Rothe
- Heide Frank
- Johannes Kadel
- Jonas Schäfer
- Katrin Weiß
- Vincent Voß
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/hegl_logo.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
