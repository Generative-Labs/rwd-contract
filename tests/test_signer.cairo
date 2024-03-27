use core::debug::PrintTrait;
use snforge_std::{declare, ContractClassTrait, start_prank};
use rwd_contract::erc20::IRWDDispatcher;
use rwd_contract::erc20::IRWDDispatcherTrait;

use starknet::ContractAddress;
use starknet::contract_address::Felt252TryIntoContractAddress;

fn deploy_contract(name: felt252) -> ContractAddress {
    let contract = declare(name);
    contract.deploy(@array![0x3]).unwrap()
}

#[test]
fn test(){
    let contract_address = deploy_contract('RWD');
    contract_address.print();
    let rwd_dispatcher = IRWDDispatcher { contract_address };
    // let addr_1 = 0x3.try_into().unwrap();
    start_prank(contract_address, 0x3.try_into().unwrap());
    rwd_dispatcher.mint(0x3.try_into().unwrap(), 10000, 2253918608606595569745139050112538854671405829226327562001928334642825796884, 955111328611337095722627320350084358579291562752307329181752305824017547701);
}