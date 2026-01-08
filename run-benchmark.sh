#!/bin/bash

# ==============================================================================
# CONFIGURATION
# ==============================================================================

cmd_trans() {
    lake build Benchmark.RunTrans
}

cmd_depth() {
    lake build Benchmark.RunDepth
}

OUTPUT_DIR="bench-results"
OUTPUT_TEX="benchmark_results.tex"

# Create directory
mkdir -p "$OUTPUT_DIR"

# ==============================================================================
# PARSING LOGIC
# ==============================================================================

parse_lean_output() {
    local prefix=$1
    
    # Output the variable assignments to stdout
    awk -v pre="$prefix" '
        /term size 0\)/      { size=0 }
        /term size 100\)/    { size=100 }
        /StatefulForward: false/ { algo="naive"; next }
        /StatefulForward: true/  { algo="inc"; next }
        /^\([0-9]/ { 
            # This matches the coordinate line starting with (number
            if (size==0 && algo=="naive")   print pre "NAIVE_0=\"" $0 "\""
            if (size==0 && algo=="inc")     print pre "INC_0=\"" $0 "\""
            if (size==100 && algo=="naive") print pre "NAIVE_100=\"" $0 "\""
            if (size==100 && algo=="inc")   print pre "INC_100=\"" $0 "\""
        }
    '
}

TIMEFORMAT="this took %R seconds"

echo "--- Running Benchmark: Transitivity ---"
# Capture output and evaluate it
eval $(time cmd_trans | parse_lean_output "FIG1_")


echo "--- Running Benchmark: Depth ---"
time eval $(cmd_depth | parse_lean_output "FIG2_")

{
    echo "Transitivity Benchmark"
    echo "Naive - 0"
    echo $FIG1_NAIVE_0
    echo "Inc - 0"
    echo $FIG1_INC_0
    echo "Naive - 100"
    echo $FIG1_NAIVE_100
    echo "Inc - 100"
    echo $FIG1_INC_100
    echo "Depth Benchmark"
    echo "Naive - 0"
    echo $FIG2_NAIVE_0
    echo "Inc - 0"
    echo $FIG2_INC_0
    echo "Naive - 100"
    echo $FIG2_NAIVE_100
    echo "Inc - 100"
    echo $FIG2_INC_100
} > $OUTPUT_DIR/synthBenchResults.txt

# ==============================================================================
# LATEX GENERATION
# ==============================================================================

echo "--- Generating LaTeX File ("$OUTPUT_DIR/$OUTPUT_TEX") ---"

cat << EOF > "$OUTPUT_DIR/$OUTPUT_TEX"
\documentclass{article}
\usepackage{pgfplots}
\usepackage{subcaption}
\usepackage{tikz}
\pgfplotsset{compat=1.17}

% Define shapes for the caption logic
\newcommand{\showpgfsquare}{\tikz\draw[orange, fill=none] (0,0) rectangle (1.2ex,1.2ex);}
\newcommand{\showpgfcircle}{\tikz\draw[orange, fill=none] (0,0) circle (0.7ex);}

\begin{document}

\begin{figure}
    \centering
    \begin{tikzpicture}[scale=0.75]
      \begin{axis}[
        xlabel={Number of hypotheses},
        ylabel={Time in ms},
        xmin=1, xmax=32,
        ymin=4, ymax=2^16,
        %xtick={1,2,4,8,16},
        %ytick={2^3,2^5,2^7,2^9,2^11,2^13},
        xmode=log,
        ymode=log,
        log basis x=2,
        log basis y=2,
        legend pos=north west,
        ymajorgrids=true,
        grid style=dashed,
        legend image post style={mark=}
        ]
        % -- PLOT: Size 0, Naive --
        \addplot[color=orange, mark=square, style=densely dashed, mark options={style={solid}}]
          coordinates { $FIG1_NAIVE_0 };
        
        % -- PLOT: Size 0, Incremental --
        \addplot[color=blue, mark=square]
          coordinates { $FIG1_INC_0 };
        
        % -- PLOT: Size 100, Naive --
        \addplot[color=orange, mark=o, style=densely dashed, mark options={style={solid}}]
          coordinates { $FIG1_NAIVE_100 };
        
        % -- PLOT: Size 100, Incremental --
        \addplot[color=blue, mark=o]
          coordinates { $FIG1_INC_100 };
      \end{axis}
    \end{tikzpicture}
  \end{figure}

\begin{figure}
\centering
    \begin{tikzpicture}[scale=0.75]
      \begin{axis}[
        xlabel={Depth},
        ylabel={Time in ms},
        xmin=1, xmax=5,
        ymin=8, ymax=2^10,
        xtick={1,2,3,4,5},
        ymode=log,
        log basis y=2,
        ymajorgrids=true,
        grid style=dashed
        ]
        % -- PLOT: Size 0, Naive --
        \addplot[color=orange, mark=square, style=densely dashed, mark options={style={solid}}]
          coordinates { $FIG2_NAIVE_0 };
        
        % -- PLOT: Size 0, Incremental --
        \addplot[color=blue, mark=square]
          coordinates { $FIG2_INC_0 };
        
        % -- PLOT: Size 100, Naive --
        \addplot[color=orange, mark=o, style=densely dashed, mark options={style={solid}}]
          coordinates { $FIG2_NAIVE_100 };
        
        % -- PLOT: Size 100, Incremental --
        \addplot[color=blue, mark=o]
          coordinates { $FIG2_INC_100 };
      \end{axis}
    \end{tikzpicture}
\end{figure}

\end{document}
EOF

# ==============================================================================
# COMPILATION
# ==============================================================================

if command -v pdflatex &> /dev/null; then
    echo "--- Compiling PDF ---"
    (cd "$OUTPUT_DIR" && pdflatex "$OUTPUT_TEX" > /dev/null)
    echo "Done! Generated benchmark_results.pdf"
else
    echo "Warning: pdflatex not found. The .tex file was created but not compiled."
fi
