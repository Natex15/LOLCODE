# LOLCODE Interpreter (Group 6)

A full-stack **LOLCODE** lexical analyzer, semantic analyzer, and interactive interpreter featuring a React + Vite web GUI and a Flask + WebSocket backend, as well as standalone CLI tools.

---

## Project Structure

```text
LOLCODE/
├── group6/
│   ├── backend/
│   │   ├── lol_lexemes.py      # Lexical analyzer (tokenizer)
│   │   ├── lol_semantics.py    # Semantic analyzer & runtime interpreter
│   │   ├── server.py           # Flask + WebSocket backend server
│   │   ├── requirements.txt    # Python backend dependencies
│   │   └── programs/           # Sample .lol programs available in the GUI
│   └── frontend/
│       ├── index.html          # Entry HTML
│       ├── package.json        # Frontend dependencies & scripts
│       ├── vite.config.js      # Vite dev server & API/WebSocket proxy config
│       └── src/
│           ├── App.jsx         # Main IDE interface (editor, lexemes, symbols, console)
│           ├── main.jsx        # React entry point
│           └── styles.css      # Application styling
├── lol_lexemes.py              # Standalone CLI lexical analyzer
├── lol_semantics.py            # Standalone CLI semantic analyzer & interpreter
├── LEXEME_PATTERNS.md          # Documentation of LOLCODE lexeme patterns
└── sample*.lol                 # Sample LOLCODE source files
```

---

## Prerequisites

- **Python**: 3.10 or higher (`python3` and `pip`)
- **Node.js**: 18 or higher (`node` and `npm`)

---

## Web GUI Setup & Running

You will need **two terminal windows** (one for the Flask backend and one for the Vite frontend).

### 1. Start the Backend Server (Flask)

```bash
cd group6/backend

# (Optional) Create and activate a virtual environment
python3 -m venv .venv
source .venv/bin/activate  # On Windows: .venv\Scripts\activate

# Install dependencies
pip install -r requirements.txt

# Start the server (runs on http://127.0.0.1:5000)
python3 server.py
```

### 2. Start the Frontend Dev Server (React + Vite)

In a second terminal:

```bash
cd group6/frontend

# Install dependencies
npm install

# Start the Vite development server
npm run dev
```

Open the URL shown in the terminal (default: `http://localhost:5173`) in your browser. Vite automatically proxies `/api` and `/ws` requests to `http://127.0.0.1:5000`.

---

## Command-Line (CLI) Usage

You can also run the lexical and semantic analyzers directly from the command line without starting the web server:

```bash
# Tokenize a LOLCODE file and print the lexeme table
python3 group6/backend/lol_lexemes.py sample.lol

# Run semantic analysis and execute a LOLCODE file
python3 group6/backend/lol_semantics.py sample.lol

# Run built-in unit self-tests (pass no file arguments)
python3 group6/backend/lol_lexemes.py
python3 group6/backend/lol_semantics.py
```

