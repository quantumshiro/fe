use crate::ir::SyntheticId;

pub(super) struct SymbolMangler {
    display_name: String,
}

impl SymbolMangler {
    pub(super) fn new(display_name: String) -> Self {
        Self { display_name }
    }

    pub(super) fn symbol_for<'db>(&self, id: SyntheticId<'db>) -> String {
        match id {
            SyntheticId::ContractInitEntrypoint(_) => format!("__{}_init", self.display_name),
            SyntheticId::ContractRuntimeEntrypoint(_) => {
                format!("__{}_runtime", self.display_name)
            }
            SyntheticId::ContractInitHandler(_) => {
                format!("__{}_init_contract", self.display_name)
            }
            SyntheticId::ContractRuntimeDispatchArm {
                recv_idx, arm_idx, ..
            } => {
                format!(
                    "__{}_runtime_arm_{}_{}",
                    self.display_name, recv_idx, arm_idx
                )
            }
            SyntheticId::ContractRecvArmHandler {
                recv_idx, arm_idx, ..
            } => {
                format!("__{}_recv_{}_{}", self.display_name, recv_idx, arm_idx)
            }
            SyntheticId::ContractInitCodeOffset(_) => {
                format!("__{}_init_code_offset", self.display_name)
            }
            SyntheticId::ContractInitCodeLen(_) => {
                format!("__{}_init_code_len", self.display_name)
            }
        }
    }
}
