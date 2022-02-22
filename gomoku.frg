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
            (i < 0 or i >= 5 or j < 0 or j >= 5)
                => no s.board[i][j]
        }
    }
}

pred initialState[s: State]{
    -- the board is empty
    all i, j: Int | no s.board[i][j]
    -- the first player is black
    s.nextPlayer = B
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
            else post.board[row][col] = prev.board[row][col]
    }
    -- The player needs to change
    prev.nextPlayer != post.nextPlayer
}

pred winRow[s: State, p: Player] {
    some row, col: Int | {
        s.board[add[row, 0]][col] = p
        s.board[add[row, 1]][col] = p
        s.board[add[row, 2]][col] = p
        s.board[add[row, 3]][col] = p
        s.board[add[row, 4]][col] = p
    }
}

pred winCol[s: State, p: Player] {
    some row, col: Int | {
        s.board[row][add[col, 0]] = p
        s.board[row][add[col, 1]] = p
        s.board[row][add[col, 2]] = p
        s.board[row][add[col, 3]] = p
        s.board[row][add[col, 4]] = p
    }
}

pred winDiag[s: State, p: Player] {
    {some row, col: Int | {
        s.board[add[row, 0]][add[col, 0]] = p
        s.board[add[row, 1]][add[col, 1]] = p
        s.board[add[row, 2]][add[col, 2]] = p
        s.board[add[row, 3]][add[col, 3]] = p
        s.board[add[row, 4]][add[col, 4]] = p
    }} or {
    some row, col: Int | {
        s.board[add[row, 0]][subtract[col, 0]] = p
        s.board[add[row, 1]][subtract[col, 1]] = p
        s.board[add[row, 2]][subtract[col, 2]] = p
        s.board[add[row, 3]][subtract[col, 3]] = p
        s.board[add[row, 4]][subtract[col, 4]] = p
    }}
}

pred win[s: State, p: Player] {
    winRow[s, p] or
    winCol[s, p] or
    winDiag[s, p]
}

pred trace {
    -- Initial state is initial
    some init: State | {
        no s: State | s.next = init
        initialState[init]
    }
    -- Every move is legal
    all prev, post: State | {
        {prev.next = post} => {
            /*
            {some p: Player | win[prev, p]}
                => {all row, col: Int | {
                    -- Nothing moves
                    prev.board[row][col] = post.board[row][col]
                    prev.nextPlayer = post.nextPlayer
                }}
                -- There is some move
                else {some row, col: Int | move[prev, row, col, post]}*/
            {some row, col: Int | move[prev, row, col, post]}
        }
    }
}

run {
    wellformed
    trace
} for exactly 3 State, 6 Int, 2 Player for {next is linear}