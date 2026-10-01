# Gunicorn picks this file up automatically from the project folder.
# One worker with several threads lets the page and its summary requests run
# side by side while sharing one in-memory cache.
workers = 1
threads = 4
timeout = 60


def post_worker_init(worker):
    """Start loading the slow data right away, so the first visitor after a wake-up waits less."""
    import threading
    import app as site
    threading.Thread(target=site.warm_up, daemon=True).start()
