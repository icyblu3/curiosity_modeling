#lang forge/bsl "cm" "dfz64hwblegqmenu; nhxnc2rfkjov1qjp"

abstract sig Player { }
-- Represents black and white
one sig B, W extends Player { }

sig State {
    next: lone State, 
    board: pfunc Int -> Int -> Player,
    nextPlayer: lone Player
}

pred wellformed {
    -- The board is 7x7 (subject to change)
    all s: State | {
        all i, j: Int {
            (i < 0 or i > 7 or j < 0 or j > 7)
                => no s.board[i][j]
        }
    }
}

pred initialState[s: State]{
    -- the board is empty except for the B and W in the middle
    all i, j: Int | {
        {i = 3 and j = 3} 
            => {s.board[i][j] = W}
            else {i = 3 and j = 4} 
                => {s.board[i][j] = B}
                else {i = 4 and j = 3} 
                    => {s.board[i][j] = B}
                    else {i = 4 and j = 4} 
                        => {s.board[i][j] = W}
                        else s.board[i][j]
    }
    -- the first player is black
    s.nextPlayer = B
}

pred flippedRowRight[row2: Int, col2: Int, prev: State, row: Int, col: Int, post: State] {
    col2 > col
    some colEnd: Int | {
        colEnd > col2
        prev.board[row][colEnd] = prev.nextPlayer
        all colBetween: Int | {
            {colBetween > col and colBetween < colEnd}
            prev.board[row][colBetween] = prev.board[row2][col2]
        }
    }
}

pred flippedRowLeft[row2: Int, col2: Int, prev: State, row: Int, col: Int] {
    col2 < col
    some colEnd: Int | {
        colEnd < col2
        prev.board[row][colEnd] = prev.nextPlayer
        all colBetween: Int | {
            {colBetween < col and colBetween > colEnd}
            prev.board[row][colBetween] = prev.board[row2][col2]
        }
    }
}

pred flippedColTop[row2: Int, col2: Int, prev: State, row: Int, col: Int, post: State] {
    row2 > row
    some rowEnd: Int | {
        rowEnd > row2
        prev.board[col][rowEnd] = prev.nextPlayer
        all rowBetween: Int | {
            {rowBetween > row and rowBetween < rowEnd}
            prev.board[rowBetween][col] = prev.board[row2][col2]
        }
    }
}

pred flippedColBottom[row2: Int, col2: Int, prev: State, row: Int, col: Int] {
    row2 < row
    some rowEnd: Int | {
        rowEnd < row2
        prev.board[rowEnd][col] = prev.nextPlayer
        all rowBetween: Int | {
            {rowBetween < row and rowBetween > rowEnd}
            prev.board[rowBetween][col] = prev.board[row2][col2]
        }
    }
}

pred flipped[row2: Int, col2: Int, prev: State, row: Int, col: Int]{

    (row2 != row or col2 != col)
    -- checks if row2 col2 is flipped by row col

    -- It is the oppnent that can be flipped
    some prev.board[row2][col2]
    prev.nextPlayer != prev.board[row2][col2]

    -- Same row, col or diag

    -- If on the same row, then it is flipped when between two opposite players
    {row = row2} => {
        flippedRowRight[row2, col2, prev, row, col] or
        flippedRowLeft[row2, col2, prev, row, col]}
    -- If on the same col, then it is flipped when between two opposite players
    {col = col2} => {
        flippedColTop[row2, col2, prev, row, col] or
        flippedColBottom[row2, col2, prev, row, col]}
    -- If on the same diagonal,
}

pred move[prev: State, row: Int, col: Int, post: State] {
    -- Guard
    -- The place where the next piece is placed is empty
    no prev.board[row][col]

    -- Transition
    -- The player placed in the position specified
    -- Others do not move
    all row2, col2: Int | {
        (row = row2 and col = col2)
            => post.board[row][col] = prev.nextPlayer
            else {flipped[row2, col2, prev, row, col, post]}
                => post.board[row][col] = prev.nextPlayer
                else post.board[row][col] = prev.board[row][col]
    }
    -- The player needs to change
    prev.nextPlayer != post.nextPlayer
}