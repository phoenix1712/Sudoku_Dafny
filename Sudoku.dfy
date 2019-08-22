module Utils 
{
    method floorSqrt(x: nat) returns (y: nat) 
        ensures x >= y * y && x < (y + 1) * (y + 1)
    {
        if (x == 0 || x == 1) 
        { 
            y := x; 
        }

        var i := 1;
        var res := 1;
        
        while (res <= x)
            invariant res <= x ==> res == i * i
            invariant res > x ==> x >= (i - 1) * (i - 1) && x < i * i
            decreases  x - res
        {
            i := i + 1;
            res := i * i;
        }

        y := i - 1;
    }
}


module Sudoku 
{
    import Utils

    method isSafe(board: array2<int>, row: int, col: int, num: int) returns (v: bool)
        requires 1 < board.Length0 == board.Length1
        requires 0 <= row < board.Length0 && 0 <= col < board.Length1
    {
        var d := 0;
        var r := 0;
        var len := board.Length0;

        while (d < len)
            invariant 0 <= d <= len;
            decreases  len - d
        {
            if(board[row, d] == num) {   return false;  }
            d := d + 1;
        }

        while (r < len)
            invariant 0 <= r <= len;
            decreases  len - r
        {
            if(board[r, col] == num) {   return false;   }
            r := r + 1;
        }

        var sqrt := Utils.floorSqrt(board.Length0);
        var boxRowStart := row - row % sqrt;
        var boxColStart := col - col % sqrt;

        r := boxRowStart;
        while (r < boxRowStart + sqrt && r < len)
            invariant boxRowStart <= r <= boxRowStart + sqrt
            decreases boxRowStart + sqrt - r
        {   
            d := boxColStart;
            while (d < boxColStart + sqrt && d < len)
                invariant boxColStart <= d <= boxColStart + sqrt
                decreases boxColStart + sqrt - d
            {
                if(board[r, d] == num) {   return false;   }
                d := d + 1;
            }
            r := r + 1;
        }

        return true;

    }

    method solveSudoku(board: array2<int>, numZeros: nat) returns (v: bool) 
        requires 1 < board.Length0 == board.Length1 
        modifies board
        decreases numZeros
    {
        var n := board.Length0;
        var row := -1;
        var col := -1;
        var isEmpty := true;

        var i := 0;
        var j := 0;

        while (i < n)
            decreases n - i
        {
            while (j < n) 
                decreases  n - j
            {
                if (board[i, j] == 0)
                {
                    row := i;
                    col := j;
                    isEmpty := false;
                    break;
                }
                j := j + 1;
            }
            if !isEmpty { break; }
            i := i + 1;
        }

        if (isEmpty || numZeros == 0) {  return true;    }

        var num := 1;
        while (num <= n)
            decreases n - num
        {
            var temp1 := isSafe(board, row, col, num);
            if(temp1) 
            {
                board[row, col] := num;
                var temp2 := solveSudoku(board, numZeros - 1);
                if(temp2) {
                    return true;
                } else {
                    board[row, col] := 0;
                }
            }
            num := num + 1;
        }

        return false;
    }

    method printBoard(board: array2<int>) 
    { 
        // we got the answer, just print it 
        var r := 0;
        while r < board.Length0
            decreases board.Length0 - r
        { 
            var d := 0;
            while d < board.Length1
                decreases board.Length1 - d
            { 
                print board[r,d]; 
                print " "; 
                d := d + 1;
            } 
            print "\n" ; 
            r := r + 1; 
        } 
    } 

    method Main() 
    { 
        var board := new int[9, 9];

        var filler := [ 
                [3, 0, 6, 5, 0, 8, 4, 0, 0], 
                [5, 2, 0, 0, 0, 0, 0, 0, 0], 
                [0, 8, 7, 0, 0, 0, 0, 3, 1], 
                [0, 0, 3, 0, 1, 0, 0, 8, 0], 
                [9, 0, 0, 8, 6, 3, 0, 0, 5], 
                [0, 5, 0, 0, 9, 0, 6, 0, 0], 
                [1, 3, 0, 0, 0, 0, 2, 5, 0], 
                [0, 0, 0, 0, 0, 0, 0, 7, 4], 
                [0, 0, 5, 2, 0, 6, 3, 0, 0] 
        ];
        
        var r := 0;
        while r < board.Length0
            decreases board.Length0 - r
        { 
            var d := 0;
            while d < board.Length1
                decreases board.Length1 - d
            { 
                board[r,d] := filler[r][d];
                d := d + 1;
            } 
            r := r + 1; 
        }

        var numZeros := 0;
        r := 0;
        while r < board.Length0
            decreases board.Length0 - r
        { 
            var d := 0;
            while d < board.Length1
                decreases board.Length1 - d
            { 
                if board[r,d] == 0
                {
                    numZeros := numZeros + 1;
                }
                d := d + 1;
            } 
            r := r + 1; 
        } 

        var solved := solveSudoku(board, numZeros);
        if solved
        { 
            printBoard(board); // print solution 
        }  
        else
        { 
            print "No solution"; 
        } 
    } 
}