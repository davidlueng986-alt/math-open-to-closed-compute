FROM ubuntu:22.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl git sudo build-essential cmake ninja-build pkg-config python3 python3-pip libboost-all-dev libgmp-dev zlib1g-dev libtbb-dev nauty z3 minisat && rm -rf /var/lib/apt/lists/*
RUN python3 -m pip install --no-cache-dir --upgrade pip setuptools wheel
RUN python3 -m pip install --no-cache-dir 'numpy>=1.26,<3' 'networkx>=3,<4' 'python-sat>=1.8.dev13'
WORKDIR /tmp/sms-build
COPY jobs/erdos-64-sms-direct/setup.sh /tmp/sms-setup.sh
RUN bash /tmp/sms-setup.sh && rm -rf /tmp/sms-build /tmp/sms-setup.sh /var/lib/apt/lists/*
ENV MATH_COMPUTE_SMS_REV=464f12f
ENV PATH="/root/.local/bin:$PATH" PYTHONPATH="/root/.local/lib/python3.10/site-packages" LD_LIBRARY_PATH="/root/.local/lib"
RUN python3 -c 'from pysms.graph_builder import GraphEncodingBuilder; import pysat,networkx,numpy' && command -v smsg && command -v z3 && command -v minisat && command -v nauty-geng
WORKDIR /work
