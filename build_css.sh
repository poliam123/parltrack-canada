#!/bin/sh
# Rebuilds static/app.css from the templates. Run this whenever you change classes in templates/*.html
# or edit input.css / tailwind.config.js. You need the Tailwind standalone program once:
#   https://github.com/tailwindlabs/tailwindcss/releases/tag/v3.4.17  (download the file for your computer,
#   rename it "tailwindcss", and put it in this folder; on a Mac run: chmod +x tailwindcss)
cd "$(dirname "$0")"
./tailwindcss -c tailwind.config.js -i input.css -o static/app.css --minify
