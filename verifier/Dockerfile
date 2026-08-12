FROM python:3.12.3-slim

WORKDIR /artifact
COPY requirements.lock ./
RUN python -m pip install --no-cache-dir --require-hashes -r requirements.lock
COPY . .

ENV PYTHONPATH=/artifact/src
CMD ["python", "scripts/verify_release.py"]
