FROM ubuntu:22.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl git zstd build-essential python3 sudo && rm -rf /var/lib/apt/lists/*
ENV ELAN_HOME=/opt/elan
ENV PATH="/opt/elan/bin:$PATH"
RUN curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none && elan toolchain install leanprover/lean4:v4.36.0 && elan default leanprover/lean4:v4.36.0
RUN git clone https://github.com/leanprover-community/mathlib4.git /opt/mathlib4 && git -C /opt/mathlib4 checkout fc4f59e577feb1a4956671bc04ac18aaaf8cd842
WORKDIR /opt/mathlib4
RUN lake exe cache get && printf 'import Mathlib\n#check Nat.add_comm\n' > /tmp/smoke.lean && lake env lean /tmp/smoke.lean && rm /tmp/smoke.lean
