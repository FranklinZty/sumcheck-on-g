pub mod errors;
pub mod multilinear_polynomial;
pub mod utils;
pub mod virtual_polynomial;
pub mod virtual_polynomial_g;
pub mod sumcheck;

use subroutines::PolyIOP;
use transcript::IOPTranscript;
use crate::{
    virtual_polynomial::{VirtualPolynomial},
    sumcheck::structs::IOPProof as SumCheckProof,
    sumcheck::{verifier::interpolate_uni_poly, SumCheck},
    multilinear_polynomial::{fix_variables, scalar_mul},
    utils::mle::{matrix_to_mle, vec_to_mle},
    utils::vec::{to_F_matrix, to_F_vec},
    utils::hypercube::BooleanHypercube,
};
use std::sync::Arc;
use ark_poly::{DenseMultilinearExtension};
use ark_bls12_381::{Fr, Fq, G1Projective};
use ark_std::{One, Zero};
use std::ops::Add;
// use ark_ff::{Fp, One}; 


const num_x:usize = 2;
const num_y:usize = 2;

fn main() {
    let M = to_F_matrix::<Fr>(vec![
        vec![1, 2, 3, 4],
        vec![5, 6, 7, 8],
        vec![1, 3, 5, 7],
        vec![2, 4, 6, 8],
    ]);

    let G = to_F_vec::<Fr>(vec![1, 2, 3, 4]);

    let M_xy_mle: DenseMultilinearExtension<Fr> = matrix_to_mle(M.clone());
    let G_y_mle: DenseMultilinearExtension<Fr> = vec_to_mle(num_y, &G.clone());
    let mut G_y_virtual =
    VirtualPolynomial::new_from_mle(&Arc::new(G_y_mle.clone()), Fr::one());

    // first round sum-check
    let mut sum_Mz = DenseMultilinearExtension::<Fr> {
        evaluations: vec![Fr::zero(); M_xy_mle.evaluations.len()],
        num_vars: num_x,
    };
    let bhc = BooleanHypercube::new(num_y);
    for y in bhc.into_iter() {
        // In a slightly counter-intuitive fashion fix_variables() fixes the right-most variables of the polynomial. So
        // for a polynomial M(x,y) and a random field element r, if we do fix_variables(M,r) we will get M(x,r).
        let M_j_y = fix_variables(&M_xy_mle, &y);
        let G_y = G_y_virtual.evaluate(&y).unwrap();
        let M_j_z = scalar_mul(&M_j_y, &G_y);
        sum_Mz = sum_Mz.add(M_j_z);
    }

    let mut M_xy_virtual =
    VirtualPolynomial::new_from_mle(&Arc::new(sum_Mz.clone()), Fr::one());

    let mut GM_xy_virtual= M_xy_virtual.clone();
    GM_xy_virtual.mul_by_mle(Arc::new(G_y_mle.clone()), Fr::one()).unwrap();

    let transcript = &mut IOPTranscript::<Fr>::new(b"sumcheck-on-x");
        transcript.append_message(b"init", b"init").unwrap();

    let sumcheck_proof_x =
            <PolyIOP<Fr> as SumCheck<Fr>>::prove(&GM_xy_virtual, transcript).unwrap();
    let r_x = sumcheck_proof_x.point.clone();
    // second round sum-check
    let M_y_mle = fix_variables(&M_xy_mle, &r_x);
    let M_y_virtual =
    VirtualPolynomial::new_from_mle(&Arc::new(M_y_mle.clone()), Fr::one());

    let mut GM_y_virtual= M_y_virtual.clone();
    GM_y_virtual.mul_by_mle(Arc::new(G_y_mle.clone()), Fr::one()).unwrap();
    
    let transcript_y = &mut IOPTranscript::<Fr>::new(b"sumcheck-on-y");
        transcript_y.append_message(b"init", b"init").unwrap();

    let sumcheck_proof_y =
            <PolyIOP<Fr> as SumCheck<Fr>>::prove(&GM_y_virtual, transcript_y).unwrap();
    let r_y = sumcheck_proof_y.point.clone();

    let eval = GM_y_virtual.evaluate(&r_y).unwrap();
    println!("eval: {}", eval);
}
