# Gunicorn picks this file up automatically from the project folder.
# One worker with several threads lets the page and its summary requests run
# side by side while sharing one in-memory cache.
workers = 1
threads = 4
timeout = 60
